using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class TildeSpectralNonconcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower-half parameter exclusion for the tilde spectral trace.",
        H("TildeSpectralNonconcavity"), Blocks(
            Describe.Lean(DescribeId.Create("strict-first-variable-jensen-violation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.strict_first_variable_jensen_violation"),
                H("Strict Jensen violation on positive definite qubits"),
                StatementSource.FromAuthor(Endpoint()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/hiai2026quasigeometric")),
                Blocks(
                    Paragraph(Text("For every real weight alpha strictly between zero and one half "
                        + "and every real p > 0, there are positive definite complex 2 by 2 matrices "
                        + "A, C and B, and a real theta strictly between zero and one, such that "
                        + "the tilde spectral trace at ((1-theta) A + theta C, B) is strictly "
                        + "less than its weighted endpoint traces.")),
                    Paragraph(Text("The weighted geometric mean has its first argument as base: "
                        + "X to exponent one half times (X to exponent minus one half Y X to "
                        + "exponent minus one half) to exponent alpha times X to exponent one half. "
                        + "Set K = A to exponent minus p geometric mean of weight alpha with B "
                        + "to exponent p. The exact function T is the real trace of (K to exponent "
                        + "one half A to exponent 2p(1-alpha) K to exponent one half) to exponent "
                        + "1/p. Every matrix power is continuous functional calculus.")),
                    Paragraph(Text("At the rank-one projection P = (1/2)[[1,1],[1,1]] and "
                        + "A = diag(x,1), x > 0, let mu=(1+x to exponent p)/2 and "
                        + "nu=(1+x to exponent 2p(1-alpha))/2. The actual matrix trace is "
                        + "(mu to exponent alpha-1 times nu) to exponent 1/p. Normalizing "
                        + "A to exponent p/2 P A to exponent p/2 yields a positive semidefinite "
                        + "idempotent; its positive powers give K=mu to exponent alpha-1 P. "
                        + "The public two_point_cfc theorem evaluates the diagonal powers and "
                        + "the scaled projections. No negative power of P is used.")),
                    Paragraph(Text("Write q=p(1-2alpha)>0 and xzero=8 to exponent -1/q. "
                        + "On the interval from xzero/4 to xzero/2 the quantity mu to exponent "
                        + "alpha-1 times nu has negative derivative. Monotonicity of the outer "
                        + "positive real power gives h(a)>h(b)>0. Set theta=(h(a)-h(b))/(2h(a)) "
                        + "and c=a+(b-a)/theta. Then b=(1-theta)a+theta c, and positivity of "
                        + "h(c) gives the strict Jensen inequality. The diagonal matrix "
                        + "affine identity transfers it to the actual functional.")),
                    Paragraph(Text("For the three fixed positive definite first matrices, "
                        + "all varying powers have positive exponents. Their continuity on the "
                        + "positive semidefinite cone, trace continuity, and a single strict "
                        + "scalar gap yield one epsilon > 0 for which B=P+epsilon I is "
                        + "positive definite and the same inequality holds.")),
                    Paragraph(Text("This excludes 0<alpha<1/2 for all p>0 in Hiai Problem 5.20. "
                        + "It does not classify alpha>1/2 or the untilde family. Jeong-Kim-Tam's "
                        + "p=1 second-variable concavity concerns another variable. "
                        + "Vuong-Shudo-Osaka's alternative-mean classification concerns the "
                        + "untilde operator. The proof is a project synthesis; comparison with "
                        + "these inspected sources is not a global novelty certification."))),
                DescribeRole.Theorem))));

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

    private static Formula Endpoint()
    {
        var alpha = F.Id("alpha"); var p = F.Id("p"); var theta = F.Id("theta");
        var a = F.Id("A"); var c = F.Id("C"); var b = F.Id("B");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)),
            Seq(Mathbb, Grp(F.Id("C"))));
        var mix = Seq(Open, D(1), Minus, theta, Close, a, Plus, theta, c);
        return Seq(Forall, Sp, alpha, Comma, Sp, p, Colon, Sp, real, Comma, Esc,
            D(0), Lt, alpha, Land, Sp, alpha, Lt, new Formula.Fraction(D(1), D(2)),
            Land, Sp, D(0), Lt, p, Implies, Esc,
            Exists, Sp, a, Comma, Sp, c, Comma, Sp, b, Colon, Sp, matrix, Comma, Esc,
            Call("PosDef", a), Land, Sp, Call("PosDef", c), Land, Sp, Call("PosDef", b),
            Land, Sp, Exists, Sp, theta, Colon, Sp, real, Comma, Esc,
            D(0), Lt, theta, Land, Sp, theta, Lt, D(1), Land, Esc,
            Call("tildeTrace", alpha, p, mix, b), Lt,
            Seq(Open, D(1), Minus, theta, Close, Call("tildeTrace", alpha, p, a, b)),
            Plus, theta, Call("tildeTrace", alpha, p, c, b));
    }
}
