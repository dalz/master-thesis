{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    ocaml
    opam
    pkg-config
    gmp
    zlib
    z3
    ruby
    git

    ocamlPackages.sail

    python312Packages.psutil
  ];

  shellHook = ''
    eval $(opam env --switch=.)
    export PATH="$(pwd)/dep/msp430-gcc-9.3.1.11_linux64/bin:$PATH"
    export C_INCLUDE_PATH="$(pwd)/dep/msp430-gcc-support-files/include:$C_INCLUDE_PATH"
  '';
}

# opam switch create .
# cd dep/sail
# (apply patch)
# opam pin add sail .
# (if not committed) opam reinstall sail --working-dir
# cd ../sail-backend
# opam install . --deps-only
# dune build
# dune install


# (load "/home/ale/uni/tesi/_opam/.opam-switch/sources/sail/editors/sail-mode.el")
