BLACK='\033[0;30m'
DARKGRAY='\033[1;30m'
RED='\033[0;31m'
LIGHTRED='\033[1;31m'
GREEN='\033[0;32m'
LIGHTGREEN='\033[1;32m'
BROWNORANGE='\033[0;33m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
LIGHTBLUE='\033[1;34m'
PURPLE='\033[0;35m'
LIGHTPURPLE='\033[1;35m'
CYAN='\033[0;36m'
LIGHTCYAN='\033[1;36m'
LIGHTGRAY='\033[0;37m'
WHITE='\033[1;37m'
ENDC='\033[0m' # No Color

printc() {
    printf "${1} ${2} ${ENDC}\n"
}

printc $GREEN "=============== ORIGINAL ==============="
./original.py $1 # > orig_out
printc $GREEN "===============  GR1_MC  ==============="
./gr1_mc.py $1 # > online_out

# echo "diff:"
# diff -U3 --minimal orig_out online_out |
#   sed 's/^-/\x1b[1;31m-/;s/^+/\x1b[1;32m+/;s/^@/\x1b[1;34m@/;s/$/\x1b[0m/' |
#   diff-highlight
