{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages [ 
      (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
        version = "2.2";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v2.2";
          hash = "sha256-/Fy5EOSbVNXt6Jq0yKSnlNPW4SYfn+eCTAYFnMZrbR0=";
        };
      }))
      (agdaPackages.agda-categories.overrideAttrs (oldAttrs : {
        version = "0.2.0";
         src = fetchFromGitHub {
           repo = "agda-categories";
           owner = "agda";
           rev = "cce07616535ea228978b08adc6dd53c275491464";
           hash = "sha256-8UK0I1WO5JJLpxvm23k6xPNf2zfbckDHMscpraaozTM=";
         };

        # without this nix might use a wrong version of the stdlib to try and typecheck agda-categories
        buildInputs = [
          (agda.withPackages [
            (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
              version = "2.2";
              src = fetchFromGitHub {
                repo = "agda-stdlib";
                owner = "agda";
                rev = "v2.2";
                hash = "sha256-/Fy5EOSbVNXt6Jq0yKSnlNPW4SYfn+eCTAYFnMZrbR0=";
              };
            }))
          ])
         ];

        GHCRTS = "-M6G";
      }))
    ])
  ];

  shellHook = ''
    # ...
  '';
}
