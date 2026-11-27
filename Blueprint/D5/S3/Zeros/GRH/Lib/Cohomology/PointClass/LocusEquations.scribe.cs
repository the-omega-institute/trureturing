using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class LocusEquationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locus Equations", H("Locus Equations"),
        Blocks(
            Paragraph(Text("Projective space as functor with standard atlas; a map P^d×P¹ to P^{d+1}. Functions cutting out the locus where two points agree; basic properties.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/LocusEquations.CutsOutLocus"),
                H("CutsOutLocus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The elements f_i of R cut out the locus P at x in X(R): a map of k-algebras α: R → C kills all f_i exactly when α(x) satisfies P.")))))));
}
