using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class PhysicalHermiteTestsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical tensor Hermite functions are Schwartz eigenfunctions with compact graph approximants.",
        H("Physical Hermite Differential Tests"),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-hermite-schwartz-cutoff-tests"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/PhysicalHermiteTests.physical_hermite_tests"),
            H("Actual differential eigenaction and compact test limits"),
            StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural dimension d, positive hbar, positive coordinate masses m "
                    + "and frequencies omega, and every multi-index alpha, the normalized physical tensor "
                    + "Hermite function Phi has a complex Schwartz realization phi on real Euclidean space. "
                    + "Set ell of j equal to the square root of hbar divided by m of j times omega of j. "
                    + "Phi is the product of the probabilists Hermite polynomial of alpha of j at "
                    + "square root of two times x of j divided by ell of j, times exp of minus x of j "
                    + "squared divided by twice ell of j squared, divided by the square root of "
                    + "square root of pi times ell of j times the factorial of alpha of j.")),
                Paragraph(Text("H0 is the actual sum of minus hbar squared divided by twice the mass "
                    + "times the second coordinate derivative, plus half the mass times frequency squared "
                    + "times the coordinate squared. H0 phi equals E times phi as Schwartz functions, "
                    + "where E is the sum of hbar times omega of j times alpha of j plus one half.")),
                Paragraph(Text("Compact smooth cutoffs psi of N converge to phi in actual complex "
                    + "Lebesgue L2. Their full H0 images simultaneously converge to E times phi. "
                    + "The coordinate Gaussian dilation and polynomial multiplier give the Schwartz "
                    + "function. Two actual coordinate derivatives and the Hermite differential equation "
                    + "give the eigenaction. The cutoff commutator and squared dominated convergence "
                    + "give the two L2 limits.")),
                Paragraph(Text("Dimension zero is included: the products are one and the energy and "
                    + "differential sums are zero. Orthonormality and totality are not hypotheses or "
                    + "conclusions here. The one-dimensional differentiation proof is adapted from "
                    + "Leonardo Pedro's Timepiece; its source and full license are identified in the Lean source."))),
            DescribeRole.Theorem))));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(n), t)], b);
    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("hbar"), m = F.Id("m"), w = F.Id("omega"), a = F.Id("alpha");
        Formula j = F.Id("j"), x = F.Id("x"), n = F.Id("N"), p = F.Id("phi"), q = F.Id("psi");
        Formula r = Seq(Mathbb, Grp(F.Id("R"))), c = Seq(Mathbb, Grp(F.Id("C")));
        Formula i = Call("Fin", d), e = Call("EuclideanSpace", r, i), sch = Call("Schwartz", e, c);
        Formula en = Call("E", d, h, w, a), op = Call("H0", d, h, m, w, p), pn = new Formula.Apply(q, [n]);
        Formula hyp = And(GtThan(h, D(0)), And(All("j", i, GtThan(new Formula.Apply(m, [j]), D(0))),
            All("j", i, GtThan(new Formula.Apply(w, [j]), D(0)))));
        Formula lim = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("psi"), new Formula.TypeArrow(F.Id("Nat"), sch))],
            And(All("N", F.Id("Nat"), Call("HasCompactSupport", pn)),
                And(Call("TendstoL2", new Formula.Sequence(Call("J", pn), n, F.Id("Nat")), Call("J", p)),
                    Call("TendstoL2", new Formula.Sequence(Call("J", Call("H0", d, h, m, w, pn)), n, F.Id("Nat")),
                        new Formula.Binary(en, FormulaBinaryOperator.Multiply, Call("J", p))))));
        Formula result = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("phi"), sch)],
            And(All("x", e, Equal(new Formula.Apply(p, [x]), Call("Phi", d, h, m, w, a, x))),
                And(Equal(op, new Formula.Binary(en, FormulaBinaryOperator.Multiply, p)), lim)));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("d"), F.Id("Nat")), new(FormulaIdentifier.Create("hbar"), r),
             new(FormulaIdentifier.Create("m"), new Formula.TypeArrow(i, r)),
             new(FormulaIdentifier.Create("omega"), new Formula.TypeArrow(i, r)),
             new(FormulaIdentifier.Create("alpha"), new Formula.TypeArrow(i, F.Id("Nat")))],
            new Formula.Logic(hyp, FormulaLogicOperator.Implies, result));
    }
    private static Formula GtThan(Formula a, Formula b) => Seq(a, Sp, Gt, Sp, b);
}
