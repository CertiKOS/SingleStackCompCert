let pkgs =import <nixpkgs> {}; 
in
with pkgs;

stdenv.mkDerivation {
  name = "singlestackcompcert";

  buildInputs = with ocamlPackages; [
    ocaml menhir findlib coq_8_6
  ];

}
