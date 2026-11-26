using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MatrixOrbits;

internal sealed class SymmetricRepresentativeSeriesDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries.source_identity_literal";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/jovovic2026a333886");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generating function for symmetric-representative matrix orbits",
        H("The generating function for symmetric-representative matrix orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a333886-generating-function"),
                DeclarationHandle.Create(Result),
                H("The all-degree coefficient formula"),
                StatementSource.FromAuthor(CoefficientFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, let M_n be the four by four matrices of natural numbers " +
                    "whose four row sums and four column sums are all n. Let O_n be the quotient " +
                    "of M_n under the action of the product of two copies of S_4. A row permutation " +
                    "and a column permutation are chosen independently. The class of B is written [B]. " +
                    "A class is counted once when it contains a symmetric B. The indices i and j range " +
                    "over I = {0, 1, 2, 3}. The coefficient and the cardinality equality are in the " +
                    "rationals. The denominator is a unit because its constant coefficient is one. " +
                    "This includes n = 0, where the orbit of the zero matrix contributes one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a333886-symmetric-matrix-orbits"),
                    ResolutionKind.Proved)),
            Paragraph(Text(
                "Transpose swaps the two permutation factors. In size four, every transpose-fixed " +
                "orbit has a symmetric representative. The twisted counts split by cycle type with " +
                "multiplicities 1, 6, 3, 8, and 6. In the identity twist, the minima of the opposite " +
                "edge pairs split off three common weights. The remaining triangular cases change " +
                "the maximum weighted degree. The transposition twist first separates equal entries " +
                "by testing whether the difference size is zero. Equal entries have equal parities. " +
                "For positive differences, the parity of the size determines which reconstruction of " +
                "the residual entries applies. The other three twists are direct graded fiber counts. " +
                "The geometric weights are 1, 2, 3, or 4. Their positivity makes each natural-parameter " +
                "fiber finite and gives each geometric factor 1 - x^d constant coefficient one, " +
                "so it is a unit. The published denominator also has constant coefficient one, and " +
                "24 is a unit over the rationals. Clearing denominators in the weighted sum gives " +
                "the identity. The Fin 16 bound in the symmetrizer controls iterates on matrix " +
                "positions for arbitrary entries and margins.")))));

    private static Formula CoefficientFormula()
    {
        Formula n = FormulaDsl.Id("n"), b = FormulaDsl.Id("B"), c = FormulaDsl.Id("C"), i = FormulaDsl.Id("i"), j = FormulaDsl.Id("j");
        Formula naturals = Seq(Mathbb, Grp(FormulaDsl.Id("N")));
        Formula numerator = Seq(D(1), Minus, D(2), X(1), Plus, D(4), X(2), Minus, X(3),
            Plus, D(9), X(4), Plus, X(5), Plus, D(1, 2), X(6), Plus, D(6), X(8),
            Minus, X(9), Plus, X(10));
        Formula denominator = Seq(Factor(1, 3), Factor(2, 1), Factor(3, 2), Factor(4, 1));
        Formula symmetric = Seq(Forall, Sp, i, Comma, j, Sp, InMacro, Sp, FormulaDsl.Id("I"), Comma, Sp,
            Seq(b, Underscore, Grp(i, j)), Eq, Seq(b, Underscore, Grp(j, i)));
        Formula classes = Seq(OpenBrace, c, Sp, InMacro, Sp, Sub("O", n), Sp, Mid, Sp,
            Exists, Sp, b, Sp, InMacro, Sp, Sub("M", n), Comma, Sp, Open,
            OpenBracket, b, CloseBracket, Eq, c, Sp, Land, Sp, symmetric, Close, CloseBrace);
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Quad,
            Lvert, classes, Rvert, Sp, Eq, Sp, OpenBracket, FormulaDsl.Id("x"), Caret, Grp(n), CloseBracket,
            Frac, Grp(numerator), Grp(denominator)));
    }

    private static Formula Sub(string name, Formula sub) => Seq(FormulaDsl.Id(name), Underscore, Grp(sub));

    private static Formula X(int degree) => degree == 1
        ? FormulaDsl.Id("x")
        : Seq(FormulaDsl.Id("x"), Caret, Grp(Degree(degree)));

    private static Formula Factor(int degree, int power)
    {
        Formula term = Seq(Open, D(1), Minus, X(degree), Close);
        return power == 1 ? term : Seq(term, Caret, Grp(Degree(power)));
    }

    private static Formula Degree(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
}
