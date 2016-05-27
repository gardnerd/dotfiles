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


# Vim da best
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
DEFAULT="\e[39m"
BOLD="\e[1m"

BLACK="\e[30m"
RED="\e[31m"
GREEN="\e[32m"
YELLOW="\e[33m"
BLUE="\e[34m"
MAGENTA="\e[35m"
CYAN="\e[36m"
LIGHTGRAY="\e[37m"
DARKGRAY="\e[90m"
LIGHTRED="\e[91m"
LIGHTGREEN="\e[92m"
LIGHTYELLOW="\e[93m"
LIGHTBLUE="\e[94m"
LIGHTMAGENTA="\e[95m"
LIGHTCYAN="\e[96m"
WHITE="\e[97m"

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

function parse_git_branch () {
  git branch 2> /dev/null | sed -e '/^[^*]/d' -e 's/* \(.*\)/ (\1)/'
}

# Bash prompt with git branch
GIT_LOCAL_BRANCH="\$(git branch &>/dev/null && echo -n '<')\$(basename \$(git symbolic-ref -q HEAD 2>/dev/null) 2>/dev/null)\$(git branch &>/dev/null && echo -n '>')"
export PS1="[\[$BOLD\]\h \[$GREEN\]$GIT_LOCAL_BRANCH \[$BLUE\]\W\[$RESET\]]$ "

export TERM=xterm-256color
xrdb $HOME/.Xresources
