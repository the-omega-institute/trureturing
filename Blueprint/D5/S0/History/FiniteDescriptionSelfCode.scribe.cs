using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class FiniteDescriptionSelfCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite descriptions correspond exactly to their natural-number self-codes.",
        H("Finite Description Self-Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-descriptions-have-lossless-self-codes"),
                DeclarationHandle.Create("D5/S0/History/FiniteDescriptionSelfCode.finite_description_self_encoding_bijective"),
                H("Finite descriptions have lossless self-codes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Operatorname, Grp(F.Id("selfEncoding")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite low-level description is represented by a finite bit string. " +
                    "Its code space is not all natural numbers by assertion, but the subtype " +
                    "consisting exactly of natural numbers in the encoder's range. The formal " +
                    "equivalence sends each description to its natural code together with the " +
                    "range witness, and its inverse recovers the original description. Hence " +
                    "the self-encoding map is injective and surjective onto the typed code " +
                    "space. This strengthens the source atom's membership notation into a " +
                    "lossless correspondence without claiming that every natural number is a " +
                    "description code.")),
                    Paragraph(Text(
                        "The pinned library was searched first. It already supplies the exact " +
                        "encoding-range equivalence as Encodable.equivRangeEncode and bundled " +
                        "bijectivity as Equiv.bijective, so the Lean proof is a declared thin " +
                        "honest wrapper rather than a second encoding proof. Searches for " +
                        "finiteDescriptionSelfCode, kernelSelfCode, and selfEncoding found no " +
                        "dedicated upstream theorem. The source atom is structural and carries " +
                        "no numerical certificate."))),
                DescribeRole.Theorem))));
}
