using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

// Source statement: Nilava Metya and Satyaki Mukherjee, arXiv:2609.38243v1,
// section 4.3, Conjecture 4.7 and equations (21)-(22), CC BY-SA 4.0.
internal sealed class IndependentConvolutionL1MinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/TotalVariation/metya2026uniformity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full L1 deviation of independent finite convolution from uniform has an attained exact minimum.",
        H("Independent finite convolution: the exact L1 minimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordinary-natural-index-convolution"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/IndependentConvolutionL1Minimum.ordinaryConvolution"),
                H("Ordinary independent convolution"),
                StatementSource.FromAuthor(OrdinaryConvolutionStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For real arrays p and q on Fin n, the coefficient at natural k is the sum "
                    + "of p(i)q(j) over i+j=k. The indices use ordinary natural addition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("independent-convolution-full-l1"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/IndependentConvolutionL1Minimum.fullL1"),
                H("Full L1 deviation"),
                StatementSource.FromAuthor(FullL1Statement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Sum the absolute deviations from 1/(2n-1) over every natural output "
                    + "index k below 2n-1. This is the full L1 norm.")),
                    Paragraph(Text(
                        "Here W_n is 2*n-1 computed by natural subtraction; range(W_n) "
                        + "contains every k from zero through W_n-1. The denominator is "
                        + "cast to the reals, and division is real division. As in Lean, "
                        + "division by zero has value zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("metya-mukherjee-conjecture-four-seven"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result"),
                H("Attained minimum for all real simplex factors and every n at least three"),
                StatementSource.FromAuthor(MinimumStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write Delta_n for the closed real standard simplex stdSimplex R (Fin n):")),
                    new DocumentBlock.DisplayFormula(ClosedSimplexStatement()),
                    Paragraph(Text(
                        "IsLeast includes membership at the displayed value and a lower bound "
                        + "for every member of the value set. Thus it includes attainment as "
                        + "well as the universal lower bound.")),
                    Paragraph(Text(
                        "For every natural n at least three, 1/(2n-1) is the least element "
                        + "of the set of fullL1 values of pairs in the closed real standard "
                        + "simplex on Fin n. Zero entries, irrational entries and asymmetric "
                        + "factors are included.")),
                    Paragraph(Text(
                        "The target is Conjecture 4.7 in section 4.3 of Nilava Metya and "
                        + "Satyaki Mukherjee, Approximate Uniformity in Finite Convolution "
                        + "Models, arXiv:2609.38243v1, equation (21). The source is available "
                        + "at https://arxiv.org/html/2609.38243v1#S4.Thmlemma7 under "
                        + "CC BY-SA 4.0. The attaining pair is the parameter-one member "
                        + "of its equation (22): with m=n-1 and t=1/(2n-1), p assigns "
                        + "one half to each endpoint, q(0)=t and q(j)=2t for j>0.")),
                    Paragraph(Text(
                        "A zero output coefficient supplies the lower bound directly. "
                        + "Otherwise the actual product of the two generating functions "
                        + "crosses the nonpositive real axis on the ray of angle pi/m. "
                        + "A trigonometric coefficient certificate gives the sharp bound; "
                        + "a crossing of radius greater than one is transported by "
                        + "reversing the output at the fixed width 2m+1. The attaining "
                        + "output equals t/2 at zero, 3t/2 at m, and t elsewhere. "
                        + "The theorem asserts no classification of all equality cases. "
                        + "Source and literature boundaries are recorded in "
                        + "Problems/metya-mukherjee-independent-convolution-l1.md."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("metya-mukherjee-independent-convolution-l1"),
                    ResolutionKind.Proved)))));
    private static Formula OrdinaryConvolutionStatement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
        Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, To, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Sp,
        Forall, Sp, F.Id("k"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak,
        Operatorname, Grp(F.Id("ordinaryConvolution")), Open, F.Id("n"), Comma,
        F.Id("p"), Comma, F.Id("q"), Comma, F.Id("k"), Close, Eq,
        Sum, Underscore, Grp(F.Id("i"), Comma, F.Id("j"), Colon,
            Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, Comma, Sp,
            Operatorname, Grp(F.Id("val")), Open, F.Id("i"), Close, Plus,
            Operatorname, Grp(F.Id("val")), Open, F.Id("j"), Close, Eq, F.Id("k")), Sp,
        F.Id("p"), Open, F.Id("i"), Close, Sp, F.Id("q"), Open, F.Id("j"), Close, Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula FullL1Statement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
        Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, To, Sp,
        Mathbb, Grp(F.Id("R")), Comma, RowBreak,
        F.Id("W"), Underscore, Grp(F.Id("n")), Eq,
        Operatorname, Grp(F.Id("Nat"), Dot, F.Id("sub")), Open, D(2), F.Id("n"), Comma, D(1), Close,
        Comma, RowBreak,
        Operatorname, Grp(F.Id("fullL1")), Open, F.Id("n"), Comma, F.Id("p"), Comma,
        F.Id("q"), Close, Eq,
        Sum, Underscore, Grp(F.Id("k"), InMacro, Sp,
            Operatorname, Grp(F.Id("range")), Open, F.Id("W"), Underscore, Grp(F.Id("n")), Close), Sp,
        Left, Bar, Operatorname, Grp(F.Id("ordinaryConvolution")), Open, F.Id("n"), Comma,
        F.Id("p"), Comma, F.Id("q"), Comma, F.Id("k"), Close, Minus,
        Frac, Grp(D(1)), Grp(F.Id("W"), Underscore, Grp(F.Id("n"))), Right, Bar, Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula MinimumStatement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        D(3), Le, Sp, F.Id("n"), Rightarrow, RowBreak,
        Operatorname, Grp(F.Id("IsLeast")), Left, Open,
        Left, OpenBrace, F.Id("v"), Colon, Sp, Mathbb, Grp(F.Id("R")), Bar,
        Exists, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
        Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, To, Sp,
        Mathbb, Grp(F.Id("R")), Comma, Sp,
        F.Id("p"), InMacro, Sp, Delta, Underscore, Grp(F.Id("n")), Land, Sp,
        F.Id("q"), InMacro, Sp, Delta, Underscore, Grp(F.Id("n")), Land, Sp,
        Operatorname, Grp(F.Id("fullL1")), Open, F.Id("n"), Comma, F.Id("p"), Comma,
        F.Id("q"), Close, Eq, F.Id("v"), Right, CloseBrace, Comma, Sp,
        Frac, Grp(D(1)), Grp(D(2), F.Id("n"), Minus, D(1)), Right, Close, Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula ClosedSimplexStatement() => Disp(Seq(
        Delta, Underscore, Grp(F.Id("n")), Eq, Left, OpenBrace,
        F.Id("x"), Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close,
        To, Sp, Mathbb, Grp(F.Id("R")), Bar,
        Open, Forall, Sp, F.Id("i"), Colon, Sp, Operatorname, Grp(F.Id("Fin")),
        Open, F.Id("n"), Close, Comma, Sp, D(0), Le, Sp,
        F.Id("x"), Open, F.Id("i"), Close, Close, Land, Sp,
        Sum, Underscore, Grp(F.Id("i"), Colon, Sp, Operatorname, Grp(F.Id("Fin")),
            Open, F.Id("n"), Close), Sp, F.Id("x"), Open, F.Id("i"), Close, Eq, D(1),
        Right, CloseBrace, Dot));
}
