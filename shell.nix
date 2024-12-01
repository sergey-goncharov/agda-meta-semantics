{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages [ 
      (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
        version = "2.0";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v2.0";
          hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
        };
      }))
      (agdaPackages.agda-categories.overrideAttrs (oldAttrs : {
        version = "0.2.0";
         src = fetchFromGitHub {
           repo = "agda-categories";
           owner = "agda";
           rev = "4aea83ae7128e0aa761d46a092050d0355f545af";
           hash = "sha256-/h0KeRkEc1bW//P/I4p61FGFIR03W7dC//WmEDFruk0=";
         };

        # without this nix might use a wrong version of the stdlib to try and typecheck agda-categories
        buildInputs = [
          (agda.withPackages [
            (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
              version = "2.0";
              src = fetchFromGitHub {
                repo = "agda-stdlib";
                owner = "agda";
                rev = "v2.0";
                hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
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
