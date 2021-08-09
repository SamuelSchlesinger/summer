{ mkDerivation, base, generics-sop, lib, vector }:
mkDerivation {
  pname = "summer";
  version = "0.2.0.1";
  src = ./.;
  libraryHaskellDepends = [ base generics-sop vector ];
  testHaskellDepends = [ base ];
  description = "An implementation of extensible products and sums";
  license = lib.licenses.mit;
}
