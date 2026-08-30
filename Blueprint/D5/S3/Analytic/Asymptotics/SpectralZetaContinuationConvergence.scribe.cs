using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class SpectralZetaContinuationConvergenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear spectral density yields a convergent spectral series and its meromorphic continuation.",
        H("Spectral Zeta Continuation With Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-density-spectral-zeta-continuation-with-convergence"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence."
                        + "linear_density_spectral_zeta_continuation_with_convergence"),
                H("Linear density gives convergence, continuation, and residue"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let lambda be a positive strictly increasing real spectrum with finite "
                            + "sublevel sets. Its counting function N_lambda(u) counts the indices "
                            + "whose spectral value is at most u, and the density hypothesis is "
                            + "N_lambda(u)-c u=O(1) at infinity.")),
                    Paragraph(Text(
                        "The named continued spectral zeta function is meromorphic on Re(s)>0 "
                            + "and agrees with the displayed spectral Dirichlet series on Re(s)>1. "
                            + "The statement separately exposes summability of the exact complex "
                            + "terms lambda(n)^(-s) throughout that initial half-plane, so the "
                            + "displayed series is not merely a totalized infinite sum.")),
                    Paragraph(Text(
                        "The continuation also has residue c at s=1, expressed as the exact "
                            + "punctured-neighborhood limit of (s-1) times the continuation. The "
                            + "proof reuses the frozen continuation, residue, and convergence "
                            + "declarations without duplicating their proof bodies."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula lambda = LambdaLower;
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula s = F.Id("s");
        Formula zeta = new Formula.Subscript(F.Id("Z"), lambda);
        Formula continued = new Formula.Subscript(F.Id("Zc"), lambda);
        Formula counting = new Formula.Subscript(F.Id("N"), lambda);
        Formula spectrumType = Seq(natural, To, real);
        Formula positive = Seq(
            Forall, Sp, Typed(n, natural), Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(lambda, n));
        Formula sublevel = Seq(
            OpenBrace, n, Sp, InMacro, Sp, natural, Sp, Mid, Sp,
            Apply(lambda, n), Sp, Leq, Sp, u, CloseBrace);
        Formula locallyFinite = Seq(
            Forall, Sp, Typed(u, real), Comma, Sp, Call("Finite", sublevel));
        Formula density = Call(
            "IsBigO",
            F.Id("atTop"),
            Seq(u, Sp, Mapsto, Sp,
                Apply(counting, u), Sp, Minus, Sp, c, Sp, u),
            Seq(u, Sp, Mapsto, Sp, D(1)));
        Formula spectralTerm = Seq(
            Open, Apply(lambda, n), Colon, complex, Close,
            Caret, Grp(Minus, s));
        Formula series = Seq(
            Sum, Underscore, Grp(Typed(n, natural)), Sp, spectralTerm);
        Formula zetaDefinition = Seq(Apply(zeta, s), Sp, Colon, Eq, Sp, series);
        Formula countingDefinition = Seq(
            Apply(counting, u), Sp, Colon, Eq, Sp, Call("card", sublevel));
        Formula continuedDefinition = Seq(
            Apply(continued, s), Sp, Colon, Eq, Sp,
            Call("continuedSpectralZeta", lambda, c, s));
        Formula positiveHalfPlane = Seq(
            OpenBrace, s, Sp, InMacro, Sp, complex, Sp, Mid, Sp,
            D(0), Sp, Lt, Sp, Re, Open, s, Close, CloseBrace);
        Formula meromorphic = Call("MeromorphicOn", continued, positiveHalfPlane);
        Formula agreement = Seq(
            Forall, Sp, Typed(s, complex), Comma, Sp,
            D(1), Sp, Lt, Sp, Re, Open, s, Close, Sp, Rightarrow, Sp,
            Apply(continued, s), Sp, Eq, Sp, Apply(zeta, s));
        Formula convergence = Seq(
            Forall, Sp, Typed(s, complex), Comma, Sp,
            D(1), Sp, Lt, Sp, Re, Open, s, Close, Sp, Rightarrow, Sp,
            Call("Summable", Seq(
                Open, Typed(n, natural), Close, Sp, Mapsto, Sp, spectralTerm)));
        Formula puncturedAtOne = Call(
            "nhdsWithin",
            D(1),
            Seq(complex, Sp, Setminus, Sp, OpenBrace, D(1), CloseBrace));
        Formula residue = Call(
            "Tendsto",
            Seq(Open, Typed(s, complex), Close, Sp, Mapsto, Sp,
                Open, s, Sp, Minus, Sp, D(1), Close, Sp, Apply(continued, s)),
            puncturedAtOne,
            Call("nhds", Seq(Open, c, Colon, complex, Close)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(lambda, spectrumType), Comma, Sp, Typed(c, real), Semi),
            Seq(Grp(), zetaDefinition, Semi),
            Seq(Grp(), countingDefinition, Semi),
            Seq(Grp(), continuedDefinition, Semi),
            Seq(Grp(), Open, positive, Close, Sp, Land, Sp,
                Call("StrictMono", lambda), Sp, Land),
            Seq(Grp(), Open, locallyFinite, Close, Sp, Land, Sp,
                density, Sp, Rightarrow),
            Seq(Grp(), Open, meromorphic, Sp, Land, Sp, agreement, Close, Sp, Land),
            Seq(Grp(), Open, convergence, Close, Sp, Land),
            Seq(Grp(), residue, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
