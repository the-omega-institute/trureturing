using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class CompletedNativeCanonicalCodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CompletedNativeCanonicalCoding", H("Canonical coding of the native completion"), Blocks(
            Describe.Lean(DescribeId.Create("completed-native-canonical-coding"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CompletedNativeCanonicalCoding.canonical_coding"),
                H("Maximal atomic collapse and independent expansion are inverse"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The native domain is the existing unrestricted CompletionTree, with equality at every finite address, its actual substitution rho, its finite atomic iterates and its actual leafless Omega. Code is the unrestricted final coalgebra with natural-number leaves and ordered binary branches. In particular it includes nonregular infinite trees and arbitrary mixtures of finite leaves and leafless subtrees. codeOmega is the all-branch value, not a separate leaf label.")),
                    Paragraph(Text("Reduced excludes the atomic sibling collision ([n+1],[n]) at every reached address. Since fork codeOmega codeOmega equals codeOmega extensionally, the second collision has no retained pair distinct from that value. The final clause states this exclusion explicitly. Collapse tests whether the entire encountered native subtree is atomic before descending, so primitive occurrences are precisely maximal finite atomic subtrees. At every other native pair, both children and their order are retained.")),
                    Paragraph(Text("Expansion is an independent total corecursor: primitive n expands to the existing atomic n, while code branches expand to native ordered branches. Its additional native state copies finite atomic expansions without using collapse or a chosen inverse. The theorem proves that collapse lands in Reduced, both inverse identities on the full indicated domains, injectivity and surjectivity onto all reduced codes, preservation of reduction under every natural shift, intertwining of every actual rho iterate with label addition, and exact uniqueness of the code of Omega.")),
                    Paragraph(Text("The arbitrary-code atomic reflection in the proof rules out a reduced branch expanding to a finite atom. The inverse identities use finite-address extensionality and the pinned final-coalgebra bisimulation principle. The theorem supplies a semantic representation, with no algorithm for deciding atomicity of arbitrary infinite inputs and no assertion of integer-code-prefix continuity. Its primary output is an unrestricted structural equivalence, rather than bounded enumeration, a checker, a numeric reduction or a certified finite instance. No external literature novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
}
