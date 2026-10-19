using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class ResolvedCountWeakValueDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/wisemansteinberghallaji2023weakvalue");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every resolved coherent-state weak value differs from the no-click value by the count times the single-photon weak value.",
        H("Resolved-count weak values"), Blocks(
            Describe.Lean(DescribeId.Create("resolved-count-claim"), DeclarationHandle.Create("D5/S3/Quantum/ResolvedCountWeakValue.claim"), H("The all-count proposition"), StatementSource.FromAuthor(Disp(Eqn(Q("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Section V, page 6: \"This supports earlier approximate results which suggested that if a photon-number resolving detector were used, the weak value post-selected on detecting m photons would exceed the no-click weak value by precisely m times the single-photon number. We leave a rigorous proof of this conjecture for future work.\" The encoding has k+1 modes, with mode 0 probed and detected; A and B are arbitrary passive evolutions. Alpha is nonzero, m is a natural count, and all conditional values require nonzero probabilities. For m=0 the difference is zero without a single-photon denominator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("resolved-count-result"), DeclarationHandle.Create("D5/S3/Quantum/ResolvedCountWeakValue.result"), H("The resolved-count identity"), StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Number insertion creates one excitation in the coherent field. Its detected-mode contribution is proportional to m, while the ignored modes contribute a term independent of m. Subtracting the zero-count value cancels that term; scaling the input amplitude cancels from the remaining ratio. A positive count with nonzero probability also guarantees a nonzero single-photon probability."))), DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("wiseman-steinberg-hallaji-2023-resolved-count-weak-values"), ResolutionKind.Proved)))));
    private static Formula ClaimBody()
    {
        var a = X("A"); var b = X("B"); var alpha = X("alpha"); var m = X("m");
        var hm = X("hM"); var hzero = X("hZero"); var hone = X("hOne");
        var zeroProb = Ne(Call("coherentProbability", a, b, alpha, D(0)), D(0));
        var oneProb = Ne(Call("singleProbability", a, b, Cast(D(1), Call("Fin", D(2)))), D(0));
        var difference = Sub(Call("coherentWeakValue", a, b, alpha, m, hm), Call("coherentWeakValue", a, b, alpha, D(0), hzero));
        return All("k", Nat(), All("A", Call("LinearIsometryEquiv", Complex(), Call("EuclideanSpace", Complex(), Call("Fin", Succ(X("k")))), Call("EuclideanSpace", Complex(), Call("Fin", Succ(X("k"))))), All("B", Call("LinearIsometryEquiv", Complex(), Call("EuclideanSpace", Complex(), Call("Fin", Succ(X("k")))), Call("EuclideanSpace", Complex(), Call("Fin", Succ(X("k"))))), All("alpha", Complex(),
            Imp(Ne(alpha, D(0)), All("m", Nat(), All("hM", Ne(Call("coherentProbability", a, b, alpha, m), D(0)),
                Ex("hZero", zeroProb, Call("ite", Eqn(m, D(0)), Eqn(difference, D(0)), Ex("hOne", oneProb,
                    Eqn(difference, Mul(Cast(m, Complex()), Call("singleWeakValue", a, b, Cast(D(1), Call("Fin", D(2))), hone)))))))))))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula X(string s) => F.Id(s);
    private static Formula Q(string s)
    {
        var parts = s.Split('.');
        var tokens = new List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(X(s), Sp, Colon, Sp, t)), Comma, Sp, Parenthesized(b));
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists, Sp, Parenthesized(Seq(X(s), Sp, Colon, Sp, t)), Comma, Sp, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Succ(Formula k) => Add(k, D(1));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Sp, Colon, Sp, t));
}
