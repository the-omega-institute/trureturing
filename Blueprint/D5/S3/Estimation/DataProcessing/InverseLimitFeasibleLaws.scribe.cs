using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InverseLimitFeasibleLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasibility is detected by all level laws.",
        H("Feasibility is detected by all level laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("feasible-level-correspondence"),
                DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws.feasible_iff_all_levels"),
                H("Feasibility is detected by all level laws"),
                StatementSource.FromAuthor(Disp(Seq(Call("feasible", F.Id("Q")), Sp, Iff, Sp, Forall, Sp, F.Id("l"), Comma, Sp, Call("feasible", Call("push", F.Id("l"), F.Id("Q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A feasible probability has full mass on the prescribed legal support, every node marginal equal to the prescribed marginal probability, and zero expected cycle excess.")),
                    Paragraph(Text("For a probability on tuples of threads, completed feasibility is equivalent to feasibility of all actual finite projections. The completed legal support is the intersection of the legal support cylinders. The finite marginal probabilities are the actual projections of the completed marginal probability.")),
                    Paragraph(Text("Countable intersections transfer full support. Equality of every finite projection determines each completed node marginal by the full-event total-variation identity. The expected-excess characterization transfers the final condition. No support-preservation assumption is needed for this correspondence about an already completed law."))),
                DescribeRole.Theorem))));
}
