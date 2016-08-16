# .bashrc

# Check to see if interactive shell
[ -z "$PS1" ] && return

#########################
# Source global definitions
#########################
if [ -f /etc/bashrc ]; then
    . /etc/bashrc
fi

# tools
if [ "$HOSTNAME" = "fpga-2015-a-linux" ]; then
    source /tools/gerfpga/latest.env_var.sh
    source /tools/xilinx/Vivado/2016.1.env_var.sh
fi

# Turn on completion in interactive
if [ -f /etc/bash_completion ]; then
    . /etc/bash_completion
fi


# best editor
export EDITOR=vim

# use vi binds in shell
set -o vi

# Add to PATH
PATH=$HOME/bin:$PATH:$HOME/.local/bin
export PATH

# Newly created files have read access for everyone and write access for me
umask 0022

# Some color definitions
RESET="\e[0m"
BOLD="\e[1m"

GREEN="\e[32m"
BLUE="\e[34m"

#########################
# Aliases
#########################
alias ls='ls --color'

# long list with hidden files
alias ll='ls -la'

# Force the confirmation when deleting/overwriting files
alias rm='rm -i'
alias cp='cp -i'
alias mv='mv -i'

############################
# Functions and other stuff
############################

# Enable Fuzzy Find
[ -f ~/.fzf.bash ] && source ~/.fzf.bash

function parse_git_branch () {
  git branch 2> /dev/null | sed -e '/^[^*]/d' -e 's/* \(.*\)/ (\1)/'
}

# Bash prompt with git branch
GIT_LOCAL_BRANCH="\$(git branch &>/dev/null && echo -n '<')\$(basename \$(git symbolic-ref -q HEAD 2>/dev/null) 2>/dev/null)\$(git branch &>/dev/null && echo -n '>')"
export PS1="[\[$BOLD\]\h \[$GREEN\]$GIT_LOCAL_BRANCH \[$BLUE\]\W\[$RESET\]]$ "

export TERM=xterm-256color
xrdb $HOME/.Xresources
