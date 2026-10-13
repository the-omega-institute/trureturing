using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Monotonicity;

internal sealed class FiniteExceptionalValuesMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity and nonnegative derivatives outside finitely many values imply interval monotonicity.",
        H("Monotonicity with Finitely Many Exceptional Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monotone-on-icc-off-finite-values"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity."
                    + "monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values"),
                H("Nonnegative derivatives away from exceptional values"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be a real-valued function continuous on the closed interval "
                        + "[a,b], and let S be a finite set of real values. At every interior "
                        + "point t for which f(t) is outside S, assume there is a real r such "
                        + "that HasDerivAt f r t and r is nonnegative. Then f is nondecreasing "
                        + "on [a,b]: whenever x and y belong to this interval and x is at "
                        + "most y, f(x) is at most f(y). The endpoints a and b are arbitrary; "
                        + "a reversed interval is empty, and a singleton interval also "
                        + "satisfies the conclusion.")),
                    Paragraph(Text(
                        "The finiteness assumption concerns values, not domain points. "
                        + "The preimage of S can be infinite, and the derivative condition "
                        + "imposes no requirement there. For example, f(x) = max(0,x) on "
                        + "[-1,1] has S = {0} and preimage [-1,0]. It is continuous, has "
                        + "derivative 1 wherever its value is outside S, and is monotone, "
                        + "although it is not differentiable at zero. This illustrates the "
                        + "criterion without requiring a finite exceptional set of inputs.")),
                    Paragraph(Text(
                        "Suppose instead that x is at most y but f(y) is strictly below "
                        + "f(x). Finiteness of S gives levels u and v strictly between "
                        + "f(y) and f(x), with u below v and with the entire open value "
                        + "interval (u,v) disjoint from S. The finite-set induction "
                        + "constructs such a gap by retaining a smaller interval on one "
                        + "side of each additional exceptional value.")),
                    Paragraph(Text(
                        "Continuity and the intermediate value theorem make the level-u "
                        + "set in [x,y] nonempty. This level set is compact, so it has a "
                        + "first point c. Within [x,c], the level-v set is likewise "
                        + "nonempty and compact; let d be its last point. Then x is at "
                        + "most d, d is strictly below c, c is at most y, f(d) = v and "
                        + "f(c) = u. If an interior point of (d,c) had value at most u, "
                        + "the intermediate value theorem would give an earlier level-u "
                        + "crossing, contradicting the choice of c. If it had value at "
                        + "least v, it would give a later level-v crossing before c, "
                        + "contradicting the choice of d. Thus all interior values lie "
                        + "strictly in (u,v).")),
                    Paragraph(Text(
                        "Every point of (d,c) is therefore an interior point of [a,b] "
                        + "whose value avoids S. Its nonnegative HasDerivAt witness "
                        + "gives differentiability and a nonnegative value of deriv. "
                        + "The mean-value monotonicity theorem, "
                        + "monotoneOn_of_deriv_nonneg, applies on [d,c] and yields "
                        + "f(d) at most f(c). This says v is at most u, contradicting "
                        + "the chosen gap. Equivalently, the descending secant would "
                        + "force a negative derivative by the mean value theorem.")),
                    Paragraph(Text(
                        "An intended application is to a weighted extended-angle scalar "
                        + "function. Such an application must supply continuity, a finite "
                        + "set of exceptional angle values, and the nonnegative native "
                        + "derivative at every interior point avoiding those values. "
                        + "The native derivative formula and the right-inverse identity "
                        + "needed for that application remain unproved by this generic "
                        + "lemma. The conclusion here is the stated interval criterion; "
                        + "native and source-global monotonicity require those additional "
                        + "mathematical steps."))),
                DescribeRole.Theorem))));

    private static Formula MonotonicityFormula()
    {
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula f = F.Id("f");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula s = F.Id("S");
        Formula t = F.Id("t");
        Formula r = F.Id("r");
        Formula derivative = All("t", real,
            Implies(F.Seq(t, F.Sp, F.InMacro, F.Sp, Call("Ioo", a, b)),
                Implies(F.Seq(F.Neg, F.Sp, F.Open,
                        Call("f", t), F.Sp, F.InMacro, F.Sp, s, F.Close),
                    Exists("r", real,
                        F.Seq(Call("HasDerivAt", f, r, t),
                            F.Sp, F.Land, F.Sp,
                            F.D(0), F.Sp, F.Leq, F.Sp, r)))));

        Formula criterion = Implies(Call("Finite", s),
            Implies(Call("ContinuousOn", f, Call("Icc", a, b)),
                Implies(derivative, Call("MonotoneOn", f, Call("Icc", a, b)))));
        return F.Disp(All("f", F.Seq(real, F.Sp, F.To, F.Sp, real),
            All("a", real, All("b", real, All("S", Call("Set", real), criterion)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(F.Forall, F.Sp, Binder(name, type), F.Comma, F.Sp, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        F.Seq(F.Exists, F.Sp, Binder(name, type), F.Comma, F.Sp, body);

    private static Formula Binder(string name, Formula type) =>
        F.Seq(F.Open, F.Id(name), F.Sp, F.Colon, F.Sp, type, F.Close);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        F.Seq(F.Open, hypothesis, F.Close, F.Sp, F.Rightarrow, F.Sp, conclusion);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }
            pieces.Add(arguments[index]);
        }
        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
