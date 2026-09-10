using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RieszBaezDuarteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/RieszBaezDuarte.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/cislo2008riesz");
    private static Formula X => F.Id("x");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula N => F.Id("n");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nplus => Par(Seq(N, Plus, D(1)));
    private static Formula Weight => Quot(Call("moebius", Nplus), Pow(Nplus, D(2)));
    private static Formula Base => Par(Seq(D(1), Minus, Quot(D(1), Pow(Nplus, D(2)))));
    private static Formula ZetaReal => Seq(Re, Sp,
        Call("riemannZeta", Seq(D(2), J, Plus, D(2))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal even zeta values define the Riesz function and the Baez-Duarte "
            + "sequence. Their exponential generating series and signed Moebius series converge "
            + "to the corresponding transforms.",
        H("Riesz and Baez-Duarte Identities"),
        Blocks(
            Paragraph(Text(
                "The zeta function is the complex Riemann zeta function; natural arguments "
                    + "are viewed as complex numbers. Its values at the positive even integers "
                    + "are real and nonzero. The arithmetic Moebius function retains its signed "
                    + "integer values, viewed in the reals. HasSum denotes convergence of the "
                    + "entire real series to its specified value.")),
            Describe.Lean(DescribeId.Create("riesz"), DeclarationHandle.Create(Prefix + "riesz"),
                H("The Riesz function"),
                StatementSource.FromAuthor(Disp(All(X, Real,
                    Equal(Call("riesz", X), Seq(X, Sp,
                        Sum, Underscore, Grp(J, Eq, D(0)), Caret, Grp(Infty), Sp,
                        Quot(Seq(Pow(Par(Seq(Minus, D(1))), J), Sp, Pow(X, J)),
                            Seq(J, Bang, Sp, ZetaReal))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The defining series is absolutely convergent for every real argument. "
                        + "The absolute reciprocal coefficients are uniformly bounded by the "
                        + "sum of the positive reciprocal-square series; the exponential series "
                        + "then provides a summable majorant."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("baez-duarte"),
                DeclarationHandle.Create(Prefix + "baezDuarte"), H("The discrete coefficients"),
                StatementSource.FromAuthor(Disp(All(K, Nat,
                    Equal(Call("baezDuarte", K), Seq(
                        Sum, Underscore, Grp(J, Eq, D(0)), Caret, Grp(K), Sp,
                        Quot(Seq(Pow(Par(Seq(Minus, D(1))), J), Sp, Call("choose", K, J)),
                            ZetaReal)))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The finite binomial transform is defined at every natural index. "
                        + "It is distinct from both Li curvature coefficients and Jensen coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("baez-duarte-moebius"),
                DeclarationHandle.Create(Prefix + "baez_duarte_hasSum_moebius"),
                H("The signed arithmetic representation"),
                StatementSource.FromAuthor(Disp(All(K, Nat,
                    HasSeries(N, Seq(Weight, Sp, Pow(Base, K)), Call("baezDuarte", K))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Apply the signed Moebius Dirichlet series at each positive even zeta "
                        + "argument, then interchange the finite binomial sum with the convergent "
                        + "arithmetic series. The first arithmetic term is included: it is one "
                        + "at index zero and zero at positive discrete indices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("riesz-generating"),
                DeclarationHandle.Create(Prefix + "riesz_generating_hasSum"),
                H("The exponential generating series"),
                StatementSource.FromAuthor(Disp(PositiveX(HasSeries(K,
                    Quot(Seq(Call("baezDuarte", K), Sp, Pow(X, K)), Seq(K, Bang)),
                    Seq(Call("exp", X), Sp, Par(Quot(Call("riesz", X), X))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The absolutely convergent Cauchy product of the exponential series and "
                        + "the original Riesz quotient series gives the identity. The factorial "
                        + "normalization turns each convolution coefficient into its finite "
                        + "binomial transform."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("riesz-moebius"),
                DeclarationHandle.Create(Prefix + "riesz_hasSum_moebius"),
                H("The arithmetic exponential kernel"),
                StatementSource.FromAuthor(Disp(PositiveX(HasSeries(N,
                    Seq(Weight, Sp, Call("exp", Quot(Seq(Minus, X), Pow(Nplus, D(2))))),
                    Quot(Call("riesz", X), X))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The two preceding identities combine after an absolutely convergent "
                        + "double-series interchange. The product of a reciprocal-square weight "
                        + "and an exponential-series term bounds each absolute summand. "
                        + "Evaluating the inner exponential and multiplying by the negative "
                        + "exponential factor gives the stated kernel, with all positive "
                        + "arithmetic indices retained."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Quot(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(Formula v, Formula domain, Formula body) =>
        Seq(Forall, Sp, v, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula PositiveX(Formula body) =>
        All(X, Real, Seq(D(0), Lt, X, Sp, Rightarrow, Sp, body));
    private static Formula HasSeries(Formula index, Formula term, Formula value) =>
        Call("HasSum", Seq(Par(Seq(index, Colon, Nat)), Sp, Mapsto, Sp, term), value);
}
