using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class WidePrimeWindowMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-tail mass on wide real intervals",
        H("A uniform estimate in the right endpoint"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-wide-window-mass"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/"
                + "WidePrimeWindowMass.prime_tail_wide_window_mass"),
            H("The logarithmic lower bound and divergence when RH fails"),
            StatementSource.FromAuthor(F.Disp(Claim())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text("Let Qθ(x) be the integral of (θ(t)−t)/t² from x to infinity, "
                    + "where θ sums log p over primes p ≤ t. This is the tail in Zhao's equation (14), "
                    + "arXiv:2411.18903v2. Let N(A,B) be the integral of max(−Qθ(x),0)/√x "
                    + "from A to B.")),
                Paragraph(Text("Loning's derivation in the discussion of trureturing issue #32573 uses "
                    + "the last whole power window inside [A,B]. Put Y = B^(1/b). "
                    + "Since A ≥ 2 and b > 1, the width condition gives A ≤ Y ≤ Y^b = B. "
                    + "The reference HasWindows interface in riemann-hypothesis asks for a whole "
                    + "power window in the relevant set above each prescribed threshold. "
                    + "Here the width condition gives a whole subinterval of each measured interval, "
                    + "and nonnegativity of the integrand transfers its mass lower bound to [A,B].")),
                Paragraph(Text("If RH fails, right-half-strip reduction gives a zero with real "
                    + "part β > 1/2. For any 0 < η < β−1/2, apply the pole estimate on [Y,Y^b] "
                    + "with loss b(β−1/2−η). This gives N(A,B) ≥ B^η above a threshold on B "
                    + "alone. Since log(B/A) ≤ log B and log B = o(B^η), the discrepancy "
                    + "diverges uniformly over admissible A.")),
                Paragraph(Text("Under RH the uniform bound on the absolute logarithmic remainder "
                    + "applies to every ordered pair in the domain. If RH fails, uniform divergence "
                    + "gives a nonnegative discrepancy above the cutoff for K = 0. Below that cutoff, "
                    + "nonnegative mass and monotonicity of the logarithm give a common lower bound "
                    + "for the discrepancy."))),
            DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Implies(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Claim()
    {
        var a = F.Id("A");
        var b = F.Id("b");
        var right = F.Id("B");
        var c = F.Id("C");
        var k = F.Id("K");
        var s = F.Id("S");
        var leftDomain = Le(F.D(2), a);
        var wide = Le(new Formula.Power(a, b), right);
        var mass = Call("N", a, right);
        var logTerm = Multiply(F.D(2), Call("log", new Formula.Fraction(right, a)));

        var discrepancy = Le(k, Subtract(mass, logTerm));
        var uniform = All("K", Exists("S", All("B",
            Implies(Le(s, right), All("A", Implies(leftDomain, Implies(wide, discrepancy)))))));
        var bound = Le(Subtract(logTerm, c), mass);
        var global = Exists("C", And(Le(F.D(0), c),
            All("A", All("B", Implies(leftDomain, Implies(wide, bound))))));
        var bDomain = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, b);
        return All("b", Implies(bDomain, And(Implies(new Formula.Not(F.Id("RH")), uniform), global)));
    }
}
