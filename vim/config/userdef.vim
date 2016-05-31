" User defined scripts etc. for vim
"------------------------------------------------------------------------------
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
"------------------------------------------------------------------------------
" turn off clipboard
set clipboard=exclude:.*
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
