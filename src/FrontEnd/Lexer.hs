-- #hide
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Lexer
-- Copyright   :  (c) The GHC Team, 1997-2000
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Lexer for Haskell.
--
-----------------------------------------------------------------------------

-- ToDo: Introduce different tokens for decimal, octal and hexadecimal (?)
-- ToDo: FloatTok should have three parts (integer part, fraction, exponent) (?)
-- ToDo: Use a lexical analyser generator (lx?)

module FrontEnd.Lexer (Token(..), lexer) where

import Control.Monad
import Data.Char hiding(isSymbol)
import Data.Ratio
import qualified Data.Char
import qualified Data.Map as Map
import qualified Data.Set as Set

import FrontEnd.ParseMonad
import FrontEnd.SrcLoc
import FrontEnd.Warning
import Name.Name
import Options
import PackedString
import Util.SetLike
import qualified FlagOpts as FO

data Token
    = VarId      !Name
    | QVarId     !Name
    | ConId      !Name
    | QConId     !Name
    | VarSym     !Name
    | ConSym     !Name
    | QVarSym    !Name
    | QConSym    !Name
    | IntTok     !Integer
    | UIntTok    !Integer
    | FloatTok   !Rational
    | Character  !Char
    | UCharacter !Char
    | StringTok  String
    | UStringTok String
    | PragmaOptions [String]
    | PragmaInline  String
    | PragmaExp     String
    | PragmaRules   !Bool
    | PragmaSpecialize !Bool
    | PragmaStart String
    | PragmaEnd
-- Symbols
    | LeftParen
    | RightParen
    | LeftUParen
    | RightUParen
    | SemiColon
    | LeftCurly
    | RightCurly
    | VRightCurly -- a virtual close brace
    | LeftSquare
    | RightSquare
    | Comma
    | Underscore
    | BackQuote
-- Reserved operators
    | DotDot
    | Colon
    | DoubleColon
    | Equals
    | Backslash
    | Bar
    | LeftArrow
    | RightArrow
    | At
    | Tilde
    | DoubleArrow
    | Minus
    | Quest
    | QuestQuest
    | StarBang
    | Exclamation
    | BangExclamation
    | Star
    | Hash
    | Dot
-- Reserved Ids
    | KW_As
    | KW_Case
    | KW_Class
    | KW_Alias
    | KW_Data
    | KW_Default
    | KW_Deriving
    | KW_Do
    | KW_Else
    | KW_Hiding
    | KW_If
    | KW_Import
    | KW_In
    | KW_Infix
    | KW_InfixL
    | KW_InfixR
    | KW_Instance
    | KW_Let
    | KW_Module
    | KW_NewType
    | KW_Of
    | KW_Then
    | KW_Type
    | KW_Where
    | KW_Qualified
    | KW_Foreign
    | KW_Forall
    | KW_Exists
    | KW_Kind
    | KW_Family
    | KW_Closed
    | EOF

reserved_ops :: Map.Map Name Token
reserved_ops = procMap [
 ( "..", DotDot ),
 -- ( ":",  Colon ),
 ( "::", DoubleColon ),
 ( "=",  Equals ),
 ( "\\", Backslash ),
 ( "|",  Bar ),
 ( "<-", LeftArrow ),
 ( "->", RightArrow ),
 ( "@",  At ),
 ( "~",  Tilde ),
 ( "=>", DoubleArrow ),
 ( [chr 0x2192], RightArrow ),  -- →
 ( [chr 0x2190], LeftArrow ),   -- ←
 ( [chr 0x2237], DoubleColon ), -- ∷
 ( [chr 0x2025], DotDot ),      -- ‥
 ( [chr 0x21d2], DoubleArrow )  -- ⇒
 ]

special_varops :: Map.Map Name Token
special_varops = procMap [
 ( "-",  Minus ),	--ToDo: shouldn't be here
 ( "?",  Quest ),     --ditto
 ( "??", QuestQuest ),--ditto
 ( "*!", StarBang ),--ditto
 ( "!",  Exclamation ),	--ditto
 ( ".",  Dot ),		--ditto
 ( "*",  Star ),	--ditto
 ( "\x2605",  Star ),	--ditto
 ( "#",  Hash )		--ditto
 ]

procMap :: [(String,Token)] -> Map.Map Name Token
procMap xs = fromList $ map f xs where
    f (x,y) = (toUnqualName x,y)

reserved_ids :: Map.Map Name Token
reserved_ids = procMap [
 ( "_",         Underscore ),
 ( "case",      KW_Case ),
 ( "class",     KW_Class ),
 ( "alias",     KW_Alias ),
 ( "data",      KW_Data ),
 ( "default",   KW_Default ),
 ( "deriving",  KW_Deriving ),
 ( "do",        KW_Do ),
 ( "else",      KW_Else ),
 ( "if",    	KW_If ),
 ( "import",    KW_Import ),
 ( "in", 	KW_In ),
 ( "infix", 	KW_Infix ),
 ( "infixl", 	KW_InfixL ),
 ( "infixr", 	KW_InfixR ),
 ( "instance",  KW_Instance ),
 ( "let", 	KW_Let ),
 ( "module", 	KW_Module ),
 ( "newtype",   KW_NewType ),
 ( "of", 	KW_Of ),
 ( "then", 	KW_Then ),
 ( "type", 	KW_Type ),
 ( "\x2200",    KW_Forall ),
 ( ['∃'],       KW_Exists ),
 ( "where", 	KW_Where )
 ]

special_varids :: Map.Map Name Token
special_varids = procMap [
 ( "as", 	KW_As ),
 ( "closed", 	KW_Closed ),
 ( "qualified", KW_Qualified ),
 ( "hiding", 	KW_Hiding ),
 ( "forall",    KW_Forall )
 ]

-- these become keywords when the cooresponding extensions are enabled.
optional_ids = procOpt [
 ( "kind", KW_Kind, FO.UserKinds ),
 ( "foreign", KW_Foreign, FO.Ffi ),
 ( "family", KW_Family, FO.TypeFamilies ),
 ( "forall", KW_Forall, FO.Forall ),
 ( "exists", KW_Exists, FO.Exists),
 ( "!"     , BangExclamation, FO.BangPatterns )
 ]

procOpt xs = Map.fromList [ (toUnqualName w,(o,k)) | (w,k,o) <- xs ]

isIdent :: Char -> Bool
isIdent  c = isAlpha c || isDigit c || c == '\'' || c == '_'

isSymbol :: Char -> Bool
isSymbol c = elem c ":!#$%&*+./<=>?@\\^|-~" || (not (isAscii c) && Data.Char.isSymbol c)

matchChar :: Char -> String -> Lex a ()
matchChar c msg = do
	s <- getInput
	if null s || head s /= c then fail msg else discard 1

-- The top-level lexer.
-- We need to know whether we are at the beginning of the line to decide
-- whether to insert layout tokens.

lexer :: (Token -> P a) -> P a
lexer = runL topLexer

topLexer :: Lex a Token
topLexer = do
    b <- pullCtxtFlag
    if b
     then setBOL >> pure VRightCurly -- the lex context state flags that we must do an empty {} - UGLY
     else do
    bol <- checkBOL
    bol <- lexWhiteSpace bol
    startToken
    if bol then lexBOL else lexToken

lexWhiteSpace :: Bool -> Lex a Bool
lexWhiteSpace bol = do
    let linePragma = do
            lexWhile (`elem` " \r\t")
            v <- lexDecimal
            lexWhile (`elem` " \r\t")
            s <- getInput
            fn <- case s of
                '"':_ -> do
                    discard 1
                    StringTok s <- lexString
                    pure (Just s)
                _ -> pure Nothing
            -- discard any "flags" at end of line ...
            lexWhile (`elem` " \r\t")
            lexWhile (isDigit)
            setFilePos (fromInteger v - 1) 1 fn
            lexWhiteSpace False
    s <- getInput
    case s of
        '{':'-':'#':s
            | pname `Map.member` pragmas -> pure bol
            | otherwise -> do
                when (pname `Set.notMember` pragmas_ignored) $
                    addWarn (UnknownPragma $ packString pname) $ "The pragma '" ++ pname ++ "' is unknown"
                discard 2
                bol <- lexNestedComment bol
                lexWhiteSpace bol
               where pname =  takeWhile isIdent (dropWhile isSpace s)
        '{':'-':_ -> do
            discard 2
            bol <- lexNestedComment bol
            lexWhiteSpace bol
        '-':'-':rest | all (== '-') (takeWhile isSymbol rest) -> do
            lexWhile (== '-')
            lexWhile (/= '\n')
            s' <- getInput
            case s' of
                -- [] -> fail "Unterminated end-of-line comment"
                _  -> lexWhiteSpace False
        '\n':'#':' ':ns -> discard 2 >> linePragma
        '\n':'#':'l':'i':'n':'e':' ':ns -> discard 6 >> linePragma
        '\n':_ -> do
            lexNewline
            lexWhiteSpace True
        '\t':_ -> do
            lexTab
            lexWhiteSpace bol
        c:_ | isSpace c -> do
            discard 1
            lexWhiteSpace bol
        _ -> pure bol

setFilePos :: Int -> Int -> Maybe String -> Lex a ()
setFilePos line column ms = do
    sl <- getSrcLoc
    let sl' = sl { srcLocLine = line, srcLocColumn = column }
    case ms of
        Just fn -> setSrcLoc sl' { srcLocFileName = packString fn }
        Nothing -> setSrcLoc sl'

lexNestedComment :: Bool -> Lex a Bool
lexNestedComment bol = do
	s <- getInput
	case s of
	    '-':'}':_ -> discard 2 >> pure bol
	    '{':'-':_ -> do
		discard 2
		bol <- lexNestedComment bol	-- rest of the subcomment
		lexNestedComment bol		-- rest of this comment
	    '\t':_    -> lexTab >> lexNestedComment bol
	    '\n':_    -> lexNewline >> lexNestedComment True
	    _:_       -> discard 1 >> lexNestedComment bol
	    []        -> fail "Unterminated nested comment"

lexRawPragma ::  String -> Lex a Token
lexRawPragma w = rp [] where
    rp c = do
	s <- getInput
	case s of
	    '#':'-':'}':_ | w == "OPTIONS"  -> discard 3 >> pure (PragmaOptions (words $ reverse c))
	--    '#':'-':'}':_ -> discard 3 >> pure (PragmaRaw w (reverse c))
	    '#':'-':'}':_ -> fail "Unknown raw pragma"
	    '\t':_    -> lexTab >> rp ('\t':c)
	    '\n':_    -> lexNewline >> rp ('\n':c)
	    x:_       -> discard 1 >> rp (x:c)
	    []        -> fail "Unterminated raw pragma"

-- When we are lexing the first token of a line, check whether we need to
-- insert virtual semicolons or close braces due to layout.

lexBOL :: Lex a Token
lexBOL = do
	pos <- getOffside
	case pos of
	    LT -> do
                -- trace "layout: inserting '}'\n" $
        	-- Set col to 0, indicating that we're still at the
        	-- beginning of the line, in case we need a semi-colon too.
        	-- Also pop the context here, so that we don't insert
        	-- another close brace before the parser can pop it.
		setBOL
		popContextL "lexBOL"
		pure VRightCurly
	    EQ ->
                -- trace "layout: inserting ';'\n" $
		pure SemiColon
	    GT ->
		lexToken

lexToken :: Lex a Token
lexToken = do
    s <- getInput
    ParseMode { parseUnboxedValues = uval, parseUnboxedTuples = utup, parseOpt = opt } <- lexParseMode
    let opt_ids = Map.mapMaybe f optional_ids where
            f (fo,k) = if fo `Set.member` optFOptsSet opt
                then Just k else Nothing
    case s of
        [] -> pure EOF
        '(':'#':_ | utup -> do
            discard 2
            pure LeftUParen
        '#':')':_ | utup -> do
            discard 2
            pure RightUParen
        '{':'-':'#':s' -> do
            discard 3
            lexWhile isSpace
            w <- lexWhile isIdent
            case normPragma w  of
                Right t -> pure t
                Left w' -> lexRawPragma w'
        '#':'-':'}':_ -> do
            discard 3
            pure PragmaEnd

	'0':c:d:_ | toLower c == 'o' && isOctDigit d -> do
			discard 2
			n <- lexOctal
			pure (IntTok n)
		  | toLower c == 'x' && isHexDigit d -> do
			discard 2
			n <- lexHexadecimal
                        rest <- getInput
                        case rest of
                            '#':_ | uval -> discard 1 >> pure (UIntTok n)
                            _ -> pure (IntTok n)

	c:_ | isDigit c -> lexDecimalOrFloat

	    | isUpper c -> lexConIdOrQual ""

	    | isLower c || c == '_' || generalCategory c == OtherLetter -> do
		(toUnqualName -> ident) <- lexWhile isIdent
		case Map.lookup ident (opt_ids `Map.union` reserved_ids `Map.union` special_varids) of
                        Just KW_Do -> setFlagDo >> pure KW_Do
			Just keyword -> pure keyword
			Nothing -> pure $ VarId ident

	    | isSymbol c -> do
		sym <- lexWhile isSymbol
                let nsym = toUnqualName sym
		pure $ case Map.lookup nsym (opt_ids `Map.union` reserved_ops `Map.union` special_varops) of
			Just t  -> t
			Nothing -> case c of
			    ':' -> ConSym nsym
			    _   -> VarSym nsym

	    | otherwise -> do
		discard 1
		case c of

		    -- First the special symbols
		    '(' ->  pure LeftParen
		    ')' ->  pure RightParen
		    ',' ->  pure Comma
		    ';' ->  pure SemiColon
		    '[' ->  pure LeftSquare
		    ']' ->  pure RightSquare
		    '`' ->  pure BackQuote
		    '{' -> do
			    pushContextL NoLayout
			    pure LeftCurly
		    '}' -> do
			    popContextL "lexToken"
			    pure RightCurly

		    '\'' -> do
			    c2 <- lexChar
			    matchChar '\'' "Improperly terminated character constant"
                            rest <- getInput
                            case rest of
                                --'#':_ | uval -> discard 1 >> pure (UIntTok $ fromIntegral $ ord c2)
                                '#':_ | uval -> discard 1 >> pure (UCharacter c2)
                                _ -> pure (Character c2)

		    '"' ->  lexString

		    _ ->    fail ("Illegal character \'" ++ show c ++ "\'\n")

lexDecimalOrFloat :: Lex a Token
lexDecimalOrFloat = do
    ParseMode { parseUnboxedValues = uval } <- lexParseMode
    let ld ds' = do
            ds <- lexWhile isDigit
            rest <- getInput
            case rest of
                ('_':_) -> discard 1 >> ld (ds' ++ ds)
                rest -> pure (ds' ++ ds,rest)
    (ds,rest) <- ld []
    case rest of
        ('.':d:_) | isDigit d -> do
            discard 1
            frac <- lexWhile isDigit
            let num = parseInteger 10 (ds ++ frac)
                decimals = toInteger (length frac)
            exponent <- do
                    rest2 <- getInput
                    case rest2 of
                        e:pm:d:_ | e `elem` "eE", (pm `elem` "+-" && isDigit d) || isDigit pm -> lexExponent
--                        'e':_ -> lexExponent
 --                       'E':_ -> lexExponent
                        _     -> pure 0
            pure (FloatTok ((num%1) * 10^^(exponent - decimals)))
        e:_ | toLower e == 'e' -> do
            exponent <- lexExponent
            pure (FloatTok ((parseInteger 10 ds%1) * 10^^exponent))
        '#':_ | uval -> discard 1 >> pure (UIntTok (parseInteger 10 ds))
        _ -> pure (IntTok (parseInteger 10 ds))

    where
	lexExponent :: Lex a Integer
	lexExponent = do
		discard 1	-- 'e' or 'E'
		r <- getInput
		case r of
		    '+':d:_ | isDigit d -> do
			discard 1
			lexDecimal
		    '-':d:_ | isDigit d -> do
			discard 1
			n <- lexDecimal
			pure (negate n)
		    d:_ | isDigit d -> lexDecimal
		    _ -> fail "Float with missing exponent"

lexConIdOrQual :: String -> Lex a Token
lexConIdOrQual qual = do
	con <- lexWhile isIdent
	let conid | null qual = ConId (toUnqualName con)
		  | otherwise = QConId (toName UnknownType (qual,con))
	    qual' | null qual = con
		  | otherwise = qual ++ '.':con
	just_a_conid <- alternative (pure conid)
	rest <- getInput
	case rest of
	  '.':c:_
	     | isLower c || c == '_' -> do	-- qualified varid?
		discard 1
		ident <- lexWhile isIdent
		case Map.lookup (toUnqualName ident) reserved_ids of
		   -- cannot qualify a reserved word
		   Just _  -> just_a_conid
		   Nothing -> pure (QVarId $ toName UnknownType (qual', ident))

	     | isUpper c -> do		-- qualified conid?
		discard 1
		lexConIdOrQual qual'

	     | isSymbol c -> do	-- qualified symbol?
		discard 1
		sym <- lexWhile isSymbol
                let nsym = toUnqualName sym
		case Map.lookup nsym reserved_ops of
		    -- cannot qualify a reserved operator
		    Just _  -> just_a_conid
		    Nothing -> pure $ case c of
			':' -> QConSym $ toName UnknownType (qual', sym)
			_   -> QVarSym $ toName UnknownType (qual', sym)

	  _ ->	pure conid -- not a qualified thing

lexChar :: Lex a Char
lexChar = do
	r <- getInput
	case r of
		'\\':_	-> lexEscape
		c:_	-> discard 1 >> pure c
		[]	-> fail "Incomplete character constant"

lexString :: Lex a Token
lexString = do
    ParseMode { parseUnboxedValues = uval } <- lexParseMode
    let loop s = do
		r <- getInput
		case r of
		    '\\':'&':_ -> do
				discard 2
				loop s
		    '\\':c:_ | isSpace c -> do
				discard 1
				lexWhiteChars
				matchChar '\\' "Illegal character in string gap"
				loop s
			     | otherwise -> do
				ce <- lexEscape
				loop (ce:s)
		    '"':'#':_ | uval -> do
				discard 2
				pure (UStringTok (reverse s))
		    '"':_ -> do
				discard 1
				pure (StringTok (reverse s))
		    c:_ -> do
				discard 1
				loop (c:s)
		    [] ->	fail "Improperly terminated string"

	lexWhiteChars :: Lex a ()
	lexWhiteChars = do
		s <- getInput
		case s of
		    '\n':_ -> do
			lexNewline
			lexWhiteChars
		    '\t':_ -> do
			lexTab
			lexWhiteChars
		    c:_ | isSpace c -> do
			discard 1
			lexWhiteChars
		    _ -> pure ()
    loop ""

lexEscape :: Lex a Char
lexEscape = do
	discard 1
	r <- getInput
	case r of

-- Production charesc from section B.2 (Note: \& is handled by caller)

		'a':_		-> discard 1 >> pure '\a'
		'b':_		-> discard 1 >> pure '\b'
		'f':_		-> discard 1 >> pure '\f'
		'n':_		-> discard 1 >> pure '\n'
		'r':_		-> discard 1 >> pure '\r'
		't':_		-> discard 1 >> pure '\t'
		'v':_		-> discard 1 >> pure '\v'
		'\\':_		-> discard 1 >> pure '\\'
		'"':_		-> discard 1 >> pure '\"'
		'\'':_		-> discard 1 >> pure '\''

-- Production ascii from section B.2

		'^':c:_		-> discard 2 >> cntrl c
		'N':'U':'L':_	-> discard 3 >> pure '\NUL'
		'S':'O':'H':_	-> discard 3 >> pure '\SOH'
		'S':'T':'X':_	-> discard 3 >> pure '\STX'
		'E':'T':'X':_	-> discard 3 >> pure '\ETX'
		'E':'O':'T':_	-> discard 3 >> pure '\EOT'
		'E':'N':'Q':_	-> discard 3 >> pure '\ENQ'
		'A':'C':'K':_	-> discard 3 >> pure '\ACK'
		'B':'E':'L':_	-> discard 3 >> pure '\BEL'
		'B':'S':_	-> discard 2 >> pure '\BS'
		'H':'T':_	-> discard 2 >> pure '\HT'
		'L':'F':_	-> discard 2 >> pure '\LF'
		'V':'T':_	-> discard 2 >> pure '\VT'
		'F':'F':_	-> discard 2 >> pure '\FF'
		'C':'R':_	-> discard 2 >> pure '\CR'
		'S':'O':_	-> discard 2 >> pure '\SO'
		'S':'I':_	-> discard 2 >> pure '\SI'
		'D':'L':'E':_	-> discard 3 >> pure '\DLE'
		'D':'C':'1':_	-> discard 3 >> pure '\DC1'
		'D':'C':'2':_	-> discard 3 >> pure '\DC2'
		'D':'C':'3':_	-> discard 3 >> pure '\DC3'
		'D':'C':'4':_	-> discard 3 >> pure '\DC4'
		'N':'A':'K':_	-> discard 3 >> pure '\NAK'
		'S':'Y':'N':_	-> discard 3 >> pure '\SYN'
		'E':'T':'B':_	-> discard 3 >> pure '\ETB'
		'C':'A':'N':_	-> discard 3 >> pure '\CAN'
		'E':'M':_	-> discard 2 >> pure '\EM'
		'S':'U':'B':_	-> discard 3 >> pure '\SUB'
		'E':'S':'C':_	-> discard 3 >> pure '\ESC'
		'F':'S':_	-> discard 2 >> pure '\FS'
		'G':'S':_	-> discard 2 >> pure '\GS'
		'R':'S':_	-> discard 2 >> pure '\RS'
		'U':'S':_	-> discard 2 >> pure '\US'
		'S':'P':_	-> discard 2 >> pure '\SP'
		'D':'E':'L':_	-> discard 3 >> pure '\DEL'

-- Escaped numbers

		'o':c:_ | isOctDigit c -> do
					discard 1
					n <- lexOctal
					checkChar n
		'x':c:_ | isHexDigit c -> do
					discard 1
					n <- lexHexadecimal
					checkChar n
		c:_ | isDigit c -> do
					n <- lexDecimal
					checkChar n

		_		-> fail "Illegal escape sequence"

    where
	checkChar n | n <= 0x01FFFF = pure (chr (fromInteger n))
	checkChar _		    = fail "Character constant out of range"

-- Production cntrl from section B.2

	cntrl :: Char -> Lex a Char
	cntrl c | c >= '@' && c <= '_' = pure (chr (ord c - ord '@'))
	cntrl _                        = fail "Illegal control character"

-- assumes at least one octal digit
lexOctal :: Lex a Integer
lexOctal = do
	ds <- lexWhile isOctDigit
	pure (parseInteger 8 ds)

-- assumes at least one hexadecimal digit
lexHexadecimal :: Lex a Integer
lexHexadecimal = do
	ds <- lexWhile isHexDigit
	pure (parseInteger 16 ds)

-- assumes at least one decimal digit
lexDecimal :: Lex a Integer
lexDecimal = do
	ds <- lexWhile isDigit
	pure (parseInteger 10 ds)

-- Stolen from Hugs's Prelude
parseInteger :: Integer -> String -> Integer
parseInteger radix ds =
	foldl1 (\n d -> n * radix + d) (map (toInteger . digitToInt) ds)

-- pragmas for which we just want the raw contents of
pragmas_raw = [["OPTIONS", "JHC_OPTIONS", "OPTIONS_JHC" ]]

-- pragmas which just have a simple string based start rule.
pragmas_std = [
    ["NOETA"],
    ["SUPERINLINE"],
    ["MULTISPECIALIZE", "MULTISPECIALISE"],
    ["SRCLOC_ANNOTATE"]
    ]

pragmas_exp = [
    ["CTYPE"]
    ]

-- pragmas with a special starting token
pragmas_parsed = [
    (["INLINE"],PragmaInline "INLINE"),
    (["NOINLINE","NOTINLINE"],PragmaInline "NOINLINE"),
    (["RULES","RULE","RULES_JHC","RULE_JHC"],PragmaRules False),
    (["CATALYST","CATALYSTS"],PragmaRules True),
    (["SPECIALIZE", "SPECIALISE"],PragmaSpecialize False),
    (["SUPERSPECIALIZE", "SUPERSPECIALISE"],PragmaSpecialize True)
    ]

pragmas = Map.fromList $ [ (y,Left x) | xs@(x:_)  <- pragmas_raw, y <- xs] ++
    [ (y,Right w) | (xs@(~(x:_)),w)  <- pragmas_all , y <- xs] where
        pragmas_all = pragmas_parsed ++
            [ (xs,PragmaStart x) | xs@(~(x:_)) <- pragmas_std ] ++
            [ (xs,PragmaExp x) | xs@(~(x:_)) <- pragmas_exp ]

pragmas_ignored = Set.fromList ["LANGUAGE", "OPTIONS_GHC", "UNPACK"]

normPragma :: String -> Either String Token
normPragma s | ~(Just v) <- Map.lookup s pragmas  = v
toUnqualName n = toName UnknownType (Nothing :: Maybe Module,n)
