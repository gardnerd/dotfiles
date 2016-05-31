source ~/.vim/config/plugin.vim
source ~/.vim/config/userdef.vim

"------------------------------------------------------------------------------
"System settings
set encoding=utf-8
set t_Co=256 " Use 256 color mode
"------------------------------------------------------------------------------
" Vim backup and history files
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
"------------------------------------------------------------------------------
" Look and feel
syntax enable
color gardnerd
filetype plugin indent on
set mouse=a " Set mouse mode 'all'
set hlsearch
set incsearch
set wrap!
set number " Display line numbers
set ruler  " Display line & column numbers on the status bar (bottom right)
set scrolloff=3 "Scroll offset of 3
set sidescrolloff=3
set bs=indent,eol,start " Set Backspace mode
"------------------------------------------------------------------------------
" TAB management
set expandtab                               " Expand new TAB characters into spaces
set tabstop=4                               " Sets how many space-width will be used for every (new) TAB added to a file
set softtabstop=4                           " Makes the spaces feel like real tabs
set shiftwidth=4                            " Set how many spaces '<<' and '>>' shift (also changes auto indent)
autocmd FileType make setlocal noexpandtab  " When editing Makefile's do not automatically expand new TAB chars into spaces
"------------------------------------------------------------------------------
" VimDiff settings
if &diff
    set diffopt+=iwhite     " Ignore white space
    set noro                " open diffs in write mode
endif
"------------------------------------------------------------------------------
" Keybinds
map gn :bn<CR>
map gp :bp<CR>
map gd :bdelete<CR>
set pastetoggle=<F12> " Toggle between ':set paste' and ':set nopaste'
"------------------------------------------------------------------------------
