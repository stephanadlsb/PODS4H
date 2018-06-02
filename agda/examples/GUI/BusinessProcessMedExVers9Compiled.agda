module GUI.BusinessProcessMedExVers9Compiled  where


open import GUI.BusinessProcessMedExVers9Example
open import GUI.RasterificFFIVers2
open import GUI.GUICompilationVers2 hiding (main)

open import GUI.GUIDefinitions

open import NativeIO renaming (NativeIO to IO;
                               nativeReturn to return;
                               _native>>=_ to _>>=_;
                               _native>>_ to _>>_)

main : IO Unit
main = do
  win <- createWindowFFI
  compile win patientRegistrationGUI
