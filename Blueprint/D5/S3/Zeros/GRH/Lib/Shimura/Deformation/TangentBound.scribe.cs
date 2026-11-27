using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Deformation;

internal sealed class TangentBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tangent Bound", H("Tangent Bound"),
        Blocks(
            Paragraph(Text("Deformations of the PEL object have at most n-1 parameters. Only the upper bound for first-order deformations is proved here, at every good place. The proof works on the finite group scheme of w-torsion with Drinfeld's lifting lemma, without p-divisible groups or crystals. Source: N. Katz, Serre–Tate local moduli, LNM 868 (1981), §1 (Drinfeld's lemma); J. Lubin, J. Tate, Formal moduli for one-parameter formal Lie groups, Bull. SMF 94 (1966); M. Harris, R. Taylor, The Geometry and Cohomology of Some Simple Shimura Varieties (2001), III.4.1.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Deformation/TangentBound.tangent_bound"),
                H("tangent_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Known result: Deformations of the PEL object have at most n-1 parameters.")))))));
}
