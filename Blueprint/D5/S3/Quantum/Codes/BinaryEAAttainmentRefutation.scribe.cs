using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEAAttainmentRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/baekwonkim2026easingleton");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No binary linear entanglement-assisted stabilizer code attains the "
        + "Singleton equality in the k = σ = 2 case.",
        H("Binary Singleton attainment is impossible"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-ea-attainment-refutation"),
                DeclarationHandle.Create("D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result"),
                H("Exclusion of exact binary Singleton attainment"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Seq(Operatorname, Grp(F.Id("Attainment")))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Baek, Won and Kim write in Section 5 of arXiv:2611.32126v1, "
                        + "“The code ⟦8,2,5;2⟧₃ attains this bound, and binary attainment is open.” "
                        + "In their Section 2 notation the binary question asks whether an "
                        + "⟦n,2,n−3;n−6⟧₂ code exists for any natural n ≥ 6, with degenerate codes included.")),
                    Paragraph(Text(
                        "Take U to be the symplectic dual of the sender's stabilizer. The claim "
                        + "Attainment requires dim U = 8 and dim (U ∩ U⊥) = 4. Every word of U "
                        + "outside U ∩ U⊥ must have weight at least n − 3, and some such word "
                        + "must have weight exactly n − 3. The weight counts nonzero coordinate pairs.")),
                    Paragraph(Text(
                        "The lower weight bound gives at most three zeros in every nonradical word. "
                        + "The radical needs at least seven occupied sites, which excludes length six. "
                        + "The attainment bridge excludes every length from eight onward and excludes "
                        + "length seven when every radical site map has rank at most one. At length seven "
                        + "a surjective radical site falls under the shortening obstruction with "
                        + "H = U ∩ U⊥ and the original symplectic form."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baek-won-kim-2026-binary-singleton-attainment"),
                    ResolutionKind.Refuted)))));
}
