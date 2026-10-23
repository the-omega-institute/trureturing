using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class PhysicalHeatGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive complex heat contractions have full right generator minus the actual Schwartz oscillator closure.",
        H("Physical Oscillator Heat Generator"),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-heat-generator"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/PhysicalHeatGenerator.physical_heat_generator"),
            H("Heat on the actual Euclidean complex L2 space"),
            StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural dimension, positive hbar and positive coordinate masses and frequencies, "
                    + "K is the closure of the Schwartz operator whose j term is minus hbar squared over twice the mass "
                    + "times the second coordinate derivative, plus one half mass times frequency squared times position squared. "
                    + "The theorem constructs a Hilbert basis represented almost everywhere by the normalized physical product Hermites, "
                    + "a family T of bounded complex linear operators, and a strongly continuous contraction semigroup S on the underlying real space. "
                    + "S is exactly the restriction of scalars of T.")),
                Paragraph(Text("At every nonnegative time the coefficient is exp of minus time times the energy, "
                    + "where the energy is the sum of hbar times frequency times occupation plus one half. "
                    + "Each bounded operator is positive in Mathlib’s sense, including symmetry and a nonnegative quadratic form. The full right difference quotient tends to v "
                    + "if and only if the pair consisting of f and minus v belongs to the graph of K. "
                    + "Any strongly continuous contraction semigroup with that same full generator graph equals S.")),
                Paragraph(Text("The multiplier bound and finite Hermite approximants establish strong continuity. "
                    + "Existing physical graph-core approximants enter the source-selected closed-generator theorem imported from ContractionSemigroup. "
                    + "Conversely, continuous coordinate maps identify every coefficient of any asserted derivative. "
                    + "Physical basis equality is discharged inside the proof from the frozen orthonormality, totality and Schwartz tests.")),
                Paragraph(Text("The source-selected general semigroup proofs are Scott Armstrong’s "
                    + "MarkovProcess revision dbade0d12c4f84179441a9df7d7147df7a8bcaa0, "
                    + "from Semigroup/Basic, StrongOperatorLimit, Generator, OrbitContinuity, GeneratorClosed and GeneratorUniqueness. "
                    + "They retain their original proof bodies and public namespace in the generic ContractionSemigroup module imported by this physical application, "
                    + "with no claim of mathematical originality. Both donor and receiver use Lean v4.33.0 and mathlib "
                    + "db584cd6d46c92f209a44c0f1c829460d327499d. The complete Apache 2.0 license is at "
                    + "docs/reports/heat-suppliers/markovprocess-LICENSE.txt; the immutable donor has no NOTICE file. "
                    + "Retire the selection when the receiver’s actually adopted mathlib pin contains equivalent declarations.")),
                Paragraph(Text("If all energies vanish, every T is the complex identity; dimension zero is included because its energy sum is empty. "
                    + "Intrinsic trace class, the hyperbolic-sine partition function, normalized Gibbs operators, "
                    + "and completed physical tensor graph and bounded-operator factorization are separate obligations. "
                    + "The O-compatible Weyl or metaplectic realization and conjugacy of the original parent Hamiltonian remain separate."))),
            DescribeRole.Theorem))));
    private static Formula And(params Formula[] clauses) => clauses.Aggregate((a, b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Map(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("hbar"), m = F.Id("m"), w = F.Id("omega");
        Formula e = F.Id("e"), t = F.Id("T"), s = F.Id("S"), other = F.Id("R");
        Formula j = F.Id("j"), n = F.Id("n"), time = F.Id("t"), f = F.Id("f"), v = F.Id("v");
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula index = Call("Fin", d), occupations = new Formula.TypeArrow(index, F.Id("Nat"));
        Formula space = Call("EuclideanSpace", real, index);
        Formula hilbert = Call("Lp", complex, D(2), Call("volume", space));
        Formula nonnegative = Call("NNReal"), semigroups = Call("StronglyContinuousContractionSemigroup", hilbert);
        Formula mj = new Formula.Apply(m, [j]), wj = new Formula.Apply(w, [j]);
        Formula energy = Call("sum", Map(j, index,
            Call("mul", h, wj, Call("add", Call("toReal", new Formula.Apply(n, [j])), new Formula.Fraction(D(1), D(2))))));
        Formula k = Call("closure", Call("schwartzOperator", d,
            Map(j, index, new Formula.Fraction(Call("pow", h, D(2)), Call("mul", D(2), mj))),
            Map(j, index, new Formula.Fraction(Call("mul", mj, Call("pow", wj, D(2))), D(2)))));
        Formula GraphLaw(Formula family) => All("f", hilbert, All("v", hilbert,
            new Formula.Logic(Call("Tendsto", Map(time, nonnegative,
                Call("smul", Call("inv", Call("toReal", time)),
                    Call("sub", new Formula.Apply(family, [time, f]), f))),
                Call("nhdsWithin", D(0), Call("Ioi", D(0))), Call("nhds", v)),
                FormulaLogicOperator.Iff,
                Call("Member", Call("Pair", f, Call("neg", v)), Call("graph", k)))));
        Formula hypotheses = And(Seq(D(0), Sp, F.Lt, Sp, h),
            All("j", index, Seq(D(0), Sp, F.Lt, Sp, mj)),
            All("j", index, Seq(D(0), Sp, F.Lt, Sp, wj)));
        Formula conclusion = And(
            All("n", occupations, Call("EventuallyEq", Call("volume", space),
                Call("representative", new Formula.Apply(e, [n])), Call("physicalHermite", d, h, m, w, n))),
            All("t", nonnegative, Equal(new Formula.Apply(s, [time]),
                Call("restrictScalars", real, new Formula.Apply(t, [time])))),
            All("t", nonnegative, All("f", hilbert, All("n", occupations,
                Equal(Call("coefficient", e, new Formula.Apply(t, [time, f]), n),
                    Call("mul", Call("ofReal", Call("exp", Call("neg", Call("mul", Call("toReal", time), energy)))),
                        Call("coefficient", e, f, n)))))),
            All("t", nonnegative, Call("IsPositive", new Formula.Apply(t, [time]))),
            GraphLaw(t),
            All("R", semigroups, new Formula.Logic(GraphLaw(other), FormulaLogicOperator.Implies, Equal(other, s))),
            new Formula.Logic(All("n", occupations, Equal(energy, D(0))), FormulaLogicOperator.Implies,
                All("t", nonnegative, Equal(new Formula.Apply(t, [time]), Call("id", complex, hilbert)))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("d"), F.Id("Nat")),
             new(FormulaIdentifier.Create("hbar"), real),
             new(FormulaIdentifier.Create("m"), new Formula.TypeArrow(index, real)),
             new(FormulaIdentifier.Create("omega"), new Formula.TypeArrow(index, real))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                new Formula.BindMany(FormulaQuantifier.Exists,
                    [new(FormulaIdentifier.Create("e"), Call("HilbertBasis", occupations, complex, hilbert)),
                     new(FormulaIdentifier.Create("T"), new Formula.TypeArrow(nonnegative,
                         Call("ContinuousLinearMap", complex, hilbert, hilbert))),
                     new(FormulaIdentifier.Create("S"), semigroups)], conclusion)));
    }
}
