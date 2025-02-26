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


    # coq
    # coqPackages.stdpp
    # coqPackages.equations
    # coqPackages.iris
  ];

  shellHook = ''
    eval $(opam env --switch=.)
    export PATH="$(pwd)/dep/msp430-gcc-9.3.1.11_linux64/bin:$PATH"
    export C_INCLUDE_PATH="$(pwd)/dep/msp430-gcc-support-files/include:$C_INCLUDE_PATH"
  '';
}

# (load "/home/ale/uni/tesi/_opam/.opam-switch/sources/sail/editors/sail-mode.el")


# opam switch create .
# opam repo add coq-released https://coq.inria.fr/opam/released
# opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

# cd dep/sail
# (apply patch)
# opam pin add sail .
# (if not committed) opam reinstall sail --working-dir

# cd ../sail-backend
# opam install . --deps-only
# dune build
# dune install

# opam install coq-katamaran








# OLD

# opam switch create .

# opam repo add coq-released https://coq.inria.fr/opam/released
# opam pin add coq 8.17.1   # latest release supported by katamaran

# cd dep/sail
# (apply patch)
# opam pin add sail .
# (if not committed) opam reinstall sail --working-dir

# cd ../sail-backend
# opam install . --deps-only
# dune build
# dune install

# cd ../stdpp
# git checkout a6387775  # needed by iris 4.1.0
# (fix make-package shebang)
# opam pin add coq-stdpp .
# opam reinstall coq-stdpp --working-dir

# cd ../iris
# git checkout iris-4.1.0  # last release supporting coq 8.18 and supported by katamaran
# opam pin add coq-iris .
# (fix make-package shebang)
# opam reinstall coq-iris --working-dir

# opam repo add katamaran https://github.com/katamaran-project/opam-repository.git
# opam install coq-katamaran





