{ sources, lib, ocamlPackages }:

let
  landmarks = sources.landmarks;
in

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "landmarks";
  version = "git";

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  src = landmarks;

  nativeBuildInputs = [ ];
  propagatedBuildInputs = [ ];

  meta = with lib; {
    inherit (landmarks) homepage description;
  };
}
