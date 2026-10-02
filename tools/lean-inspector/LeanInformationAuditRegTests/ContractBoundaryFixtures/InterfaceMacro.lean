import Lean
namespace Quality.InterfaceMacro
macro "emitNonTypeValue" : command => `(def generatedValue : Nat := 17)
emitNonTypeValue
end Quality.InterfaceMacro
