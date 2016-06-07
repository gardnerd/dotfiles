" Config for plugins
"
" This file handles all basic configuration for plugins.
"------------------------------------------------------------------------------
" Pathogen
call pathogen#infect()
"------------------------------------------------------------------------------
" Matchit
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
"------------------------------------------------------------------------------
" NERDTree
function TNERDTree()
    NERDTreeToggle
endfunction
map <F4> :call TNERDTree()<CR>
"------------------------------------------------------------------------------
" Buffergator
let g:buffergator_autoexpand_on_split = 0
let g:buffergator_sort_regime = "filepath"
let g:buffergator_autodismiss_on_select = 0
let g:buffergator_autoupdate = 1
map <F3> :BuffergatorToggle<CR>
set noequalalways
"------------------------------------------------------------------------------
" Gitgutter
let g:gitgutter_sign_column_always = 1
let g:gitgutter_diff_args = '-w'
nmap ]c <Plug>GitGutterNextHunk " Default binding
nmap [c <Plug>GitGutterPrevHunk " Default binding
nmap ,hs <Plug>GitGutterStageHunk
nmap ,hr <Plug>GitGutterUndoHunk
nmap ,hv <Plug>GitGutterPreviewHunk
"------------------------------------------------------------------------------
