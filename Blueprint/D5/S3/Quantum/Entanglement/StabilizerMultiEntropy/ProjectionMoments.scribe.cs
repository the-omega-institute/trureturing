using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class ProjectionMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover arbitrary subspace functions from quotient-code moments.",
        H("Recover arbitrary subspace functions from quotient-code moments"),
        Blocks(Describe.Lean(DescribeId.Create("physical-lattice-reconstruction"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments.physical_lattice_reconstruction"),
            H("Recover arbitrary subspace functions from quotient-code moments"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("In a finite-dimensional space over a finite field, use one diagonal density encoder for every quotient by a subspace. After row scaling, the moment at order one more than the label dimension counts tuples in an intersection. Grouping tuples by their span factors the kernel through the inclusion zeta matrix with a strictly positive diagonal of spanning-tuple counts. This proves invertibility and gives one real coefficient vector for every target scalar function, shared over all selected sets of sites."))), DescribeRole.Theorem))));
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Statement()
    {
        var x = F.Id("f"); var y = F.Id("ell"); var z = F.Id("w");
        return Disp(All("f",Call("RealFunctionsOnSubspaces"),All("ell",Call("SiteLabels"),Equal(Call("ReconstructedPhysicalMoment",y,x),Call("TargetColumnSpanFunction",x,y)))));
    }
}
