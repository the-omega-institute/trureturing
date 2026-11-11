using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class SplitQuarticIrreducibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse homogeneous multiaffine quartics are irreducible over an arbitrary field.",
        H("A support obstruction to factorization"),
        Blocks(
            Paragraph(Text("Let k be any field and let the variable labels be Fin 8. For a set I of labels, squareExponent I is the sum of the single exponents at its members.")),
            Describe.Lean(DescribeId.Create("square-exponent-coordinate"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_apply"),
                H("Coordinates of a squarefree exponent"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("squareExponent(I)(i) = if i in I then 1 else 0")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponent has coordinate one at each member of I and zero elsewhere. This identifies a squarefree monomial with its exact set of variable labels."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("square-exponent-degree"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_degree"),
                H("Degree of a squarefree exponent"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("degree(squareExponent(I)) = card(I)")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing these coordinates gives the cardinality of I. In particular, four-element sets give degree-four monomials."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("sparse-quartic-irreducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.irreducible_of_fewer_than_twenty_zeros"),
                H("The arbitrary-factor obstruction"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("homogeneous(f,4) and (forall i, degreeOf(i,f) <= 1) and card({I : card(I)=4 and coeff(f,squareExponent(I))=0}) < 20 implies Irreducible(f)")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are seventy squarefree quartic positions. Suppose fewer than twenty coefficients at these positions vanish. Then f is irreducible over k; neither algebraic closure nor characteristic zero is required.")),
                    Paragraph(Text("For an arbitrary factorization f=FG, additivity of degree in each variable forces the variable sets of F and G to be disjoint. A nonzero monomial of each factor therefore multiplies without coefficient cancellation. Homogeneity of f forces every supported monomial of F to have the same degree. Consequently every nonzero squarefree coefficient of f has the same number of labels in the variable set of F.")),
                    Paragraph(Text("Every nonempty proper cut of eight labels misses at least twenty quartic positions if a fixed intersection cardinality is imposed. This contradicts the assumed number of zero coefficients. Thus one factor must be a unit. The coefficient support argument applies to every factorization, rather than to factors of any prescribed shape."))),
                DescribeRole.Theorem))));
}
