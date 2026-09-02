using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NormalizationSystemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminating locally confluent rewrite systems expose one canonical "
            + "certified normalizer.",
        H("Certified Normalization Systems"),
        Blocks(Describe.Lean(
            DescribeId.Create("certified-normalizers-are-unique"),
            DeclarationHandle.Create(
                "D5/S0/Rewriting/NormalizationSystem.certified_normalizer_run_unique"),
            H("Certified normalizers are unique"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("N"), Comma, Sp, F.Id("M"), Colon, Sp,
                Call("CertifiedNormalizer", F.Id("S")), Comma, Sp,
                F.Id("N"), Dot, F.Id("run"), Sp, Eq, Sp,
                F.Id("M"), Dot, F.Id("run"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A normalization system packages a rewrite step together with well-founded termination and local confluence.")),
                Paragraph(Text(
                    "The existing Newman and normal-form nodes supply a canonical endpoint, reachability, irreducibility, idempotence, and invariance under generated equivalence.")),
                Paragraph(Text(
                    "A certified normalizer must return a reachable irreducible endpoint. Confluence identifies that endpoint with the canonical normal form, so any two certified normalizers agree as functions."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Rewriting/NormalFormFunction")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
