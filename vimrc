call pathogen#infect()

set dir=$HOME/.vim/my_dirs/swp                  " vim saves 'lock' files here
set backupdir=$HOME/.vim/my_dirs/bkup           " vim saves backup of files, if created, here
set undodir=$HOME/.vim/my_dirs/undodir          " vim saves undo history here
set undofile                                    " switch to turn undo history on
set undolevels=1000                             " Maximum number of changes that can be undone
set undoreload=10000                            " Maximum number lines to save for undo on a buffer reload

" Tell vim to remember certain things when we exit
"  '20  :  marks will be remembered for up to 20 previously edited files
"  "100 :  will save up to 100 lines for each register
"  :25  :  up to 25 lines of command-line history will be remembered
"  %    :  saves and restores the buffer list
"  n... :  where to save the viminfo files
"set viminfo='20,\"100,:25,%,n~/.vim/my_dirs/viminfo
set viminfo='20,\"100,:25,n~/.vim/my_dirs/viminfo

set encoding=utf-8
set t_Co=256

" The following is what provides colorization (on a terminal?)
syntax enable
set hlsearch
set incsearch                               " Turn on incremental search
set wrap!                                   " Make sure long lines are not wrapped: wrap!
set number                                 " Display line numbers
set ruler                                  " Display line & column numbers on the status bar (bottom right)
set cursorline                              " Highlight current line
" Keep 3 lines below and above the cursor
set scrolloff=3
set sidescrolloff=3

color gardnerd

"------------------------------------------------------------------------------------------
filetype plugin indent on
set bs=indent,eol,start

" TAB management
set et                                      " set expandtab     (Expand new TAB characters into spaces. How many? That's determined by ts)
set ts=4                                    " set tabstop       (Sets how many space-width will be used for every (new) TAB added to a file)
set sts=4                                   " set softtabstop   (Makes the spaces feel like real tabs)
autocmd FileType make setlocal noexpandtab  " When editing Makefile's (files of type 'make'), do not automatically expand new TAB chars into spaces, i.e. declare an exception to 'set et'.

set ai                                      " Always auto indent
set mouse=a                                 " Make sure mouse scroll (up/down) with its wheel has the effect of pressing Ctrl+e/y (move up/down in the buffer being viewed) in vim's running on console.
                                            " This also makes mouse left clicks move the cursor to the clicked spot, again in vim's running on console.


" Maps gn to switch to viewing the next buffer. The order of the buffers are as it appears when F5 is pressed - see below, where gbuf is explained)
map gn :bn<CR>
map gp :bp<CR>
map gd :bdelete<CR>


function TNERDTree()
    NERDTreeToggle
endfunction

map <F4> :call TNERDTree()<CR>
set pastetoggle=<F12>                       " Toggle between ':set paste' and ':set nopaste'.  Pasting mouse-selected multi-line text appears staggered in 'nopaste' mode. Hit F12, then paste to prevent that.

if &diff
    " Dumb hack to get Tabbar not to open on vimdiff
"    let g:Tb_MoreThanOne=5
    set diffopt+=iwhite     " Ignore white space
    set noro                " open files in write mode
else
    " Setup Tabbar plugin
    let g:buffergator_autoexpand_on_split = 0
    let g:buffergator_sort_regime = "filepath"
    let g:buffergator_autodismiss_on_select = 0
    let g:buffergator_autoupdate = 1
    map <F3> :BuffergatorToggle<CR>
    set noequalalways
endif


"------------------------------------------------------------------------------------------
" Trim trailing spaces (at the end of each line) and replace existing TAB's in the entire file with 4 spaces.
function CleanUp()
    if &fileformat != "unix"    " Force UNIX file format (I guess for new files?)
        silent! e ++ff=unix
        " For some reason the ff=unix stuff above is disabling syntax highlighting
        silent! syntax on
    endif
    silent! %s/\r//g            " Remove DOS line feeds so that file is saved in unix format
    if &filetype != "make"
        silent! %s/\t/    /g    " Replaces tab's with 4 spaces. Don't do this on Makefile's
    endif
    silent! %s/\s\+$//          " Remove trailing spaces at the end of lines
endfunction

"------------------------------------------------------------------------------------------
" Set up some auto-updating (End of ~/.vim/plugin/tabbar.vim is quite informative - Read it)
autocmd! BufWrite           *       call CleanUp()              " On save, call this function.
autocmd! BufRead,BufNewFile *.sv    set filetype=verilog
autocmd! BufRead,BufNewFile *.inc   set filetype=verilog
autocmd! FileType                   make setlocal noexpandtab

" Verilog syntax matching
filetype plugin on
source ~/.vim/plugin/matchit.vim

if exists('loaded_matchit')
let b:match_ignorecase=0
let b:match_words=
  \ '\<begin\>:\<end\>,' .
  \ '\<if\>:\<else\>,' .
  \ '\<module\>:\<endmodule\>,' .
  \ '\<class\>:\<endclass\>,' .
  \ '\<program\>:\<endprogram\>,' .
  \ '\<clocking\>:\<endclocking\>,' .
  \ '\<property\>:\<endproperty\>,' .
  \ '\<sequence\>:\<endsequence\>,' .
  \ '\<package\>:\<endpackage\>,' .
  \ '\<covergroup\>:\<endgroup\>,' .
  \ '\<primitive\>:\<endprimitive\>,' .
  \ '\<specify\>:\<endspecify\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<interface\>:\<endinterface\>,' .
  \ '\<function\>:\<endfunction\>,' .
  \ '\<task\>:\<endtask\>,' .
  \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
  \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
  \ '`ifdef\>:`elsif\>:`else\>:`endif\>,'
endif

" turn off clipboard
set clipboard=exclude:.*

" Commenting blocks of code.
autocmd FileType c,cpp,java,scala,verilog let b:comment_leader = '// '
autocmd FileType sh,ruby,python        let b:comment_leader = '# '
autocmd FileType conf,fstab            let b:comment_leader = '# '
autocmd FileType tex                   let b:comment_leader = '% '
autocmd FileType mail                  let b:comment_leader = '> '
autocmd FileType vim                   let b:comment_leader = '" '
nnoremap <silent> ,cc :<C-B>silent <C-E>s/^/<C-R>=escape(b:comment_leader,'\/')<CR>/<CR>:nohlsearch<CR>
    \:<C-B>silent <C-E>s/^\V<C-R>=escape(b:comment_leader,'\/')<CR><C-R>=escape(b:comment_leader,'\/')<CR>//eg<CR>:nohlsearch<CR>
vnoremap <silent> ,cc :<C-B>silent <C-E>s/^/<C-R>=escape(b:comment_leader,'\/')<CR>/<CR>:nohlsearch<CR>
    \:<C-B>silent <C-E>'<,'>s/^\V<C-R>=escape(b:comment_leader,'\/')<CR><C-R>=escape(b:comment_leader,'\/')<CR>//eg<CR>:nohlsearch<CR>
"------------------------------------------------------------------------------

" * and # search for next/previous of selected text when used in visual mode
xno * :<c-u>cal<SID>VisualSearch()<cr>/<cr>
xno # :<c-u>cal<SID>VisualSearch()<cr>?<cr>
fun! s:VisualSearch()
  let old = @" | norm! gvy
  let @/ = '\V'.substitute(escape(@", '\'), '\n', '\\n', 'g')
  let @" = old
endf
