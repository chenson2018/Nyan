with import <nixpkgs> { };
mkShell {
  name = "coq_8_17";
  buildInputs = [ coq_8_17 ];
}
