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

    ocamlPackages.sail

    python312Packages.psutil
  ];

  shellHook = "eval $(opam env --switch=.)";
}

# opam install sail
# install katamaran sail backend


# (load "/home/ale/uni/tesi/_opam/.opam-switch/sources/sail.0.18/editors/sail-mode.el")
