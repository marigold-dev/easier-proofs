#! /usr/bin/env bash
usage () {
    cat >&2 <<EOF
usage: $0 [<action>] [FILES] [--ignore FILES]

Where <action> can be:

* --update-ocamlformat: update all the \`.ocamlformat\` files and
  git-commit (requires clean repo).
* --check-ocamlformat: check the above does nothing.
* --help: display this and return 0.
EOF
}

## Testing for dependencies
if ! type ocamlformat > /dev/null 2>&-; then
  echo "ocamlformat is required but could not be found. Aborting."
  exit 1
fi
if ! type find > /dev/null 2>&-; then
  echo "find is required but could not be found. Aborting."
  exit 1
fi

set -e

say () {
    echo "$*" >&2
}

make_dot_ocamlformat () {
    local path="$1"
    cat > "$path" << EOF

version=0.21.1
wrap-fun-args=false
let-binding-spacing=compact
field-space=loose
break-separators=after
space-around-arrays=false
space-around-lists=false
space-around-records=false
space-around-variants=false
dock-collection-brackets=true
space-around-records=false
sequence-style=separator
doc-comments=before
margin=80
module-item-spacing=sparse
parens-tuple=always
EOF
}

declare -a source_directories

source_directories=(~/easier-proofs/src ~/easier-proofs/src/tests)

update_all_dot_ocamlformats () {
    if git diff --name-only HEAD --exit-code
    then
        say "Repository clean :thumbsup:"
    else
        say "Repository not clean, which is required by this script."
        exit 2
    fi
    interesting_directories=$(find "${source_directories[@]}" \( -name "*.ml" -o -name "*.mli"  \) -type f | sed 's:/[^/]*$::' | LC_COLLATE=C sort -u)
    for d in $interesting_directories ; do
        ofmt=$d/.ocamlformat
        case "$d" in
            ~/easier-proofs/src | \
            ~/easier-proofs/src/tests )
                make_dot_ocamlformat "$ofmt"
                ;;
            * )
                make_dot_ocamlformat "$ofmt"
                ;;
        esac
        git add "$ofmt"
    done
}


if [ $# -eq 0 ] || [[ "$1" != --* ]]; then
    say "provide one action (see --help)"
    exit 1
else
    action="$1"
    shift
fi

check_clean=false
commit=
on_files=false

case "$action" in
    "--update-ocamlformat" )
        action=update_all_dot_ocamlformats
        commit="Update .ocamlformat files" ;;
    "--check-ocamlformat" )
        action=update_all_dot_ocamlformats
        check_clean=true ;;
    "help" | "-help" | "--help" | "-h" )
        usage
        exit 0 ;;
    * )
        say "Error no action (arg 1 = '$action') provided"
        usage
        exit 2 ;;
esac

if $on_files; then
    declare -a input_files files ignored_files
    input_files=()
    while [ $# -gt 0 ]; do
        if [ "$1" = "--ignore" ]; then
            shift
            break
        fi
        input_files+=("$1")
        shift
    done

    if [ ${#input_files[@]} -eq 0 ]; then
        mapfile -t input_files <<< "$(find "${source_directories[@]}" \( -name "*.ml" -o -name "*.mli" -o -name "*.mlt" \) -type f -print)"
    fi
else
    if [ $# -gt 0 ]; then usage; exit 1; fi
    $action
fi


if $check_clean; then
    echo "Files that differ but that shouldn't:"
    git diff --name-only HEAD --exit-code
    echo "(none, everything looks good)"
fi
