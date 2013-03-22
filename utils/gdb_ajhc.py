import gdb

def _gpe(arg):
    """TOO SLOW!!!"""
    return gdb.parse_and_eval(arg)

class PrintJgcheapCommand (gdb.Command):
    """Dump Haskell heap."""
    def __init__ (self):
        super (PrintJgcheapCommand, self).__init__ ("print_jgcheap", \
                                                       gdb.COMMAND_OBSCURE)

    def _p_arena(self):
        block_used = _gpe('arena->block_used')
        block_threshold = _gpe('arena->block_threshold')
        number_gcs = _gpe('arena->number_gcs')
        print 'block_used :     ', int(block_used)
        print 'block_threshold :', int(block_threshold)
        print 'number_gcs :     ', int(number_gcs)

    def _p_free_blocks(self):
        dict_normal = {}
        dict_mono = {}
        s_block = _gpe('arena->free_blocks.slh_first')
        while int(str(s_block), 16) != 0:
            s_block_dref = s_block.dereference()
            flags = s_block_dref['flags']
            if flags & 16 == 0:
                num_ptrs = s_block_dref['u']['pi']['num_ptrs']
                size = s_block_dref['u']['pi']['size']
                key = (int(num_ptrs), int(size))
                if key not in dict_normal:
                    dict_normal[key] = 1
                else:
                    dict_normal[key] += 1
            else:
                num_ptrs = s_block_dref['u']['m']['num_ptrs']
                key = int(num_ptrs)
                if key not in dict_mono:
                    dict_mono[key] = 1
                else:
                    dict_mono[key] += 1
            s_block = s_block_dref['link']['sle_next']
        print "free normal blocks :"
        for k, v in dict_normal.iteritems():
            print ' ', k, ':',  v
        print "free monolithic blocks :"
        for k, v in dict_mono.iteritems():
            print ' ', k, ':', v

    def _p_s_cache(self):
        list_cache = []
        s_cache = _gpe('arena->caches.slh_first')
        print "list s_cache :"
        while int(str(s_cache), 16) != 0:
            s_cache_dref = s_cache.dereference()
            num_ptrs = s_cache_dref['num_ptrs']
            size = s_cache_dref['size']
            key = (int(num_ptrs), int(size))
            num_entries = s_cache_dref['num_entries']

            # collect blocks used partially
            blocks = s_cache_dref['blocks']['slh_first']
            while int(str(blocks), 16) != 0:
                blocks_dref = blocks.dereference()
                blocks = blocks_dref['link']['sle_next']

            # collect blocks used fully
            full_blocks = s_cache_dref['full_blocks']['slh_first']
            while int(str(full_blocks), 16) != 0:
                full_blocks_dref = full_blocks.dereference()
                full_blocks = full_blocks_dref['link']['sle_next']

            list_cache.append((key, {'num_entries' : int(num_entries)}))
            s_cache = s_cache_dref['next']['sle_next']
        for k, v in sorted(list_cache):
            print ' ', k, ':', v

    def invoke (self, arg, from_tty):
        self._p_arena()
        self._p_free_blocks()
        self._p_s_cache()

PrintJgcheapCommand()
