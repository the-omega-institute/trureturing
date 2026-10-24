using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalNativeConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalNativeConstruction", H("Native completed solutions of functional cases"), Blocks(
            Describe.Lean(DescribeId.Create("native-simultaneous-equations"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_solution"),
                H("The native corecursor satisfies every simultaneous equation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a system with no variable at a defining root, the constructed native vector satisfies every definition and agrees exactly with the supplied completed assignment at every undefined state. Constants and literal Omega are permitted defining roots; recursive state occurrences are below pairs. The root-link normalization theorem derives this shape from the original functional system."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-conditional-uniqueness"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_unique"),
                H("Uniqueness conditional on all free values"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every native solution with the given free assignment equals the constructed vector. Expression evaluation is a coalgebra morphism: the source equations justify each defined root, the free assignment justifies every undefined root, and ordered-pair children retain the same expression valuation. Final-coalgebra uniqueness then applies to this concrete native morphism."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-native-construction"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.original_native_construction"),
                H("Simultaneous construction, conditional uniqueness and exact reconstruction"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input is any finite functional system in the literal-Omega source syntax. Normalization and its reconstruction are obtained from that system and do not depend on parameters. There is no assumed normalized presentation or supplied solution. The conclusions hold for all natural parameter values and therefore for every value satisfying the retained arithmetic guard.")),
                    Paragraph(Text("The function native is an actual corecursor into the existing unrestricted CompletionTree. Its states are displayed expressions or native trees being copied. A defined pair emits an ordered native branch immediately. Fixed powers distribute over that branch using the actual substitution rho. Finite grounds, parameter atoms, literal Omega and arbitrary completed free assignments use their actual native values. The proof establishes composition with fixed powers and expression evaluation before deriving the simultaneous equations.")),
                    Paragraph(Text("For each assignment to undefined normalized states, native satisfies the normalized equations and has exactly those free values. It is the unique normalized solution with that assignment, by the instantiated final-coalgebra morphism law. Reconstructing it gives an original solution. Every original solution restricts to a normalized solution and is recovered by the same construction with its own free values. Erased state names may remain as unused normalized coordinates; their supplied values do not create additional original choices.")),
                    Paragraph(Text("Assigning the actual Omega to every normalized free coordinate selects a canonical original solution. Applying the retained reconstruction to each original residual preserves its full native value. All state and parameter counts, bare links, zero alias cycles and positive root cycles remain in scope. This canonical selection is a semantic construction; effective prefix computation and a complete semantic finiteness classifier require additional conclusions.")),
                    Paragraph(Text("The finite compiler is reused through a total internal encoding. Original parameter indices are shifted injectively, while one fixed divergent slot represents literal Omega, including at zero original parameters. This slot is representation data and is always interpreted divergently; its natural placeholder is fixed to zero. Decoding finite outputs removes it and returns expressions using only original grounds, parameters, powers and pairs. Every successful compilation is forced in every original solution, including the constructed one. Failure of this finite test is not asserted to imply canonical infinity.")),
                    Paragraph(Text("The mathematical inputs are native root-link normalization, the existing finite-resolution theorem, the native substitution identities and the pinned polynomial-functor final coalgebra. No free unary substitution, bare-drift contraction, bounded rank, satisfiability assumption or supplied fixed point is used. No external novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
}
