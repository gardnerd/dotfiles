" User defined scripts etc. for vim
"
" Any VimScripts or other user created functions go here.
"------------------------------------------------------------------------------
" Commenting blocks of code.
autocmd FileType c,cpp,java,scala,verilog let b:comment_leader = '// '
autocmd FileType sh,ruby,python,cmake  let b:comment_leader = '# '
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
"------------------------------------------------------------------------------
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
" Auto Cleanup after writing file
autocmd! BufWrite           *       call CleanUp()
"------------------------------------------------------------------------------
" Toggle ignore whitespaces (VimDiff or GitGutter)
function ToggleIgnoreWhite()
    if &diff
        if &diffopt =~ 'iwhite'
            set diffopt-=iwhite
            echo "-iwhite"
        elseif &diffopt !~ 'iwhite'
            set diffopt+=iwhite
            echo "+iwhite"
        endif
    else
        if g:gitgutter_diff_args =~ '-w'
            let g:gitgutter_diff_args = ''
            GitGutter
            echo "-iwhite"
        elseif g:gitgutter_diff_args !~ '-w'
            let g:gitgutter_diff_args = '-w'
            GitGutter
            echo "+iwhite"
        endif
    endif
endfunction
map <F8> :call ToggleIgnoreWhite()<CR>
"------------------------------------------------------------------------------
" Indent Python in the Google way.

setlocal indentexpr=GetGooglePythonIndent(v:lnum)

let s:maxoff = 50 " maximum number of lines to look backwards.

function GetGooglePythonIndent(lnum)

  " Indent inside parens.
  " Align with the open paren unless it is at the end of the line.
  " E.g.
  "   open_paren_not_at_EOL(100,
  "                         (200,
  "                          300),
  "                         400)
  "   open_paren_at_EOL(
  "       100, 200, 300, 400)
  call cursor(a:lnum, 1)
  let [par_line, par_col] = searchpairpos('(\|{\|\[', '', ')\|}\|\]', 'bW',
        \ "line('.') < " . (a:lnum - s:maxoff) . " ? dummy :"
        \ . " synIDattr(synID(line('.'), col('.'), 1), 'name')"
        \ . " =~ '\\(Comment\\|String\\)$'")
  if par_line > 0
    call cursor(par_line, 1)
    if par_col != col("$") - 1
      return par_col
    endif
  endif

  " Delegate the rest to the original function.
  return GetPythonIndent(a:lnum)

endfunction

let pyindent_nested_paren="&sw*2"
let pyindent_open_paren="&sw*2"
