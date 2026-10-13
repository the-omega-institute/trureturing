using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class InverseMeanVariationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse-mean trace variational formula in every finite complex dimension.",
        H("InverseMeanVariational"), Blocks(
            Describe.Lean(DescribeId.Create("norm-rpow-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_gram"),
                H("Shared column Gram spectral trace"), StatementSource.FromAuthor(Gram()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("For every finite complex square matrix A and r > 0, "
                    + "the Schatten r expression to exponent r equals tracePower (r/2) "
                    + "of A* A. This original proof is consumed by both the inverse-mean "
                    + "variational bound and reverse trace Young. It also includes empty "
                    + "dimension and singular A. The audit remains unfinished under #5214: "
                    + "no faithful enrolled template supplies the full matrix telescope "
                    + "with rigid universe reconstruction and sensitivity evidence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("norm-rpow-row-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/InverseMeanVariational.norm_rpow_rowGram"),
                H("Shared row Gram spectral trace"), StatementSource.FromAuthor(Gram(row: true)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("The original row Gram proof is public at its source. "
                    + "The inverse-mean variational formula and the actual TILDE midpoint "
                    + "classification consume this same declaration directly. No proof is "
                    + "copied and no generated private declaration name is used. Its faithful "
                    + "full-telescope audit remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the "
                    + "observational-dependence proof's CFC.one_rpow rewrite did not match "
                    + "the concrete CFC.rpow identity-matrix target. The failed attempt is "
                    + "preserved outside accepted source and is not a validated registration."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("holder-two-young"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/InverseMeanVariational.holder_two_young"),
                H("Shared two-factor Holder and Young bound"), StatementSource.FromAuthor(Young()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("The original two-factor Schatten Holder and scalar "
                    + "Young proof is public at its source for every r > 0. It is consumed "
                    + "directly by both variational formulas. These are existing mathematical "
                    + "suppliers, not additional originality claims. Its faithful full-telescope "
                    + "audit attempt remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the "
                    + "observational-dependence proof reaches a deterministic whnf timeout "
                    + "at 1000000 heartbeats, including after explicit CFC rewrites. The failed "
                    + "attempt is preserved outside accepted source and is not a validated "
                    + "registration."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variational-bound-attainment"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Hiai/InverseMeanVariational.variational_bound_and_attainment"),
                H("Universal bound and explicit optimizer"), StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/zhang2020variational")),
                Blocks(Paragraph(Text("Let X and M be positive definite square complex matrices "
                    + "and r > 0. Write R = X M inverse X. The objective at Z is twice the real "
                    + "trace of (Z* X squared Z) to exponent r/2, minus the real trace of "
                    + "(Z* M Z) to exponent r. Every spectral power uses the actual matrix "
                    + "continuous functional calculus. For every complex Z the objective is "
                    + "at most the trace of R to exponent r.")),
                    Paragraph(Text("The invertible optimizer is M inverse X, which need not "
                    + "be selfadjoint. Both Z* M Z = R and X Z = R hold at this optimizer. "
                    + "The universal bound even allows singular Z, whereas attainment uses "
                    + "an invertible Z. No commutation assumption is made on X and M.")),
                    Paragraph(Text("Factor X Z as U V, with U = X M to exponent minus one half "
                    + "and V = M to exponent one half times Z. Product Schatten Holder with "
                    + "exponents r, 2r, 2r and scalar Young give the bound. The row Gram matrix "
                    + "of U is R and the column Gram matrix of V is Z* M Z. Characteristic "
                    + "polynomial cyclicity identifies row and column spectral traces.")),
                    Paragraph(Text("For the spectral sandwich geometric mean, put "
                    + "D = X to exponent minus one half times Y times X to exponent minus "
                    + "one half, and M = X to exponent one half times D to exponent theta "
                    + "times X to exponent one half. Direct inversion gives R = X to exponent "
                    + "one half times D to exponent minus theta times X to exponent one half. "
                    + "The same bound and optimizer therefore apply to the trace power of "
                    + "this negative-exponent mean. Identifying it with the original Hiai "
                    + "inner matrix Y geometric mean of exponent one plus theta with X "
                    + "requires an additional normalized-unitary identity.")),
                    Paragraph(Text("This is a concrete specialization of Zhang's variational "
                    + "method, not a claim of mathematical originality. For Hiai's target set "
                    + "X = B to exponent p and M = X weighted geometric mean A to exponent p. "
                    + "Joint convexity still requires the Carlen-Lieb fixed-congruence trace "
                    + "convexity and the Hiai outer-power geometric-mean trace concavity. "
                    + "Neither curvature supplier is assumed by this theorem."))),
                DescribeRole.Theorem))));

    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Gram(bool row = false)
    {
        var d = F.Id("d"); var a = F.Id("A"); var r = F.Id("r");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Sp,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            a, Colon, Sp, matrix, Comma, Sp, r, Colon, Sp,
            Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp, D(0), Lt, r, Implies, Esc,
            Call("rpow", Call("schattenNorm", a, r), r), Eq,
            Call("tracePower", Frac(r, D(2)),
                row ? Seq(a, Call("adjoint", a)) : Seq(Call("adjoint", a), a)));
    }
    private static Formula Young()
    {
        var d = F.Id("d"); var u = F.Id("U"); var v = F.Id("V"); var r = F.Id("r");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var twice = Seq(D(2), r);
        Formula NormPower(Formula a, Formula q) => Call("rpow", Call("schattenNorm", a, q), q);
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Esc,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Esc,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            u, Comma, Sp, v, Colon, Sp, matrix, Comma, Esc,
            r, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc,
            D(0), Lt, r, Implies, Esc,
            D(2), NormPower(Seq(u, v), r), Minus, NormPower(v, twice), Le, NormPower(u, twice));
    }
    private static Formula Endpoint()
    {
        var d = F.Id("d"); var x = F.Id("X"); var m = F.Id("M");
        var r = F.Id("r"); var z = F.Id("Z"); var w = F.Id("W");
        var matrix = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        var inverse = Call("inverse", m);
        var bound = Call("tracePower", r, Seq(x, inverse, x));
        return Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("Level"), Comma, Esc,
            d, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma, Esc,
            x, Comma, Sp, m, Colon, Sp, matrix, Comma, Esc,
            r, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc,
            Call("PosDef", x), Land, Sp, Call("PosDef", m), Land, Sp, D(0), Lt, r,
            Implies, Esc, Exists, Sp, z, Colon, Sp, matrix, Comma, Esc,
            Call("IsUnit", z), Land, Sp, z, Eq, Seq(inverse, x), Land, Sp,
            Call("objective", r, x, m, z), Eq, bound, Land,
            Open, Forall, Sp, w, Colon, Sp, matrix, Comma, Esc,
            Call("objective", r, x, m, w), Le, bound, Close);
    }
}
