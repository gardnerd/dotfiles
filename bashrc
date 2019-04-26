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
PATH=$HOME/bin:$HOME/.cargo/bin:$PATH:$HOME/.local/bin
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

# Bash prompt with git branch and working copy
GIT_WORKING_COPY="\$(git branch &>/dev/null && basename \$(git rev-parse --show-toplevel))"
GIT_LOCAL_BRANCH="\$(git branch &>/dev/null && git rev-parse --abbrev-ref HEAD)"

# Only print if in a repo
GIT_INFO="\$(git branch &>/dev/null && echo -n $GIT_WORKING_COPY && echo -n ' <' && echo -n $GIT_LOCAL_BRANCH && echo -n '>')"

export PS1="[\[$BOLD\]\h \[$GREEN\]$GIT_INFO \[$BLUE\]\W\[$RESET\]]$ "

export TERM=xterm-256color
xrdb $HOME/.Xresources
