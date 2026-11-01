using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GuessingProbabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive operator-valued measurements define an honest supremum guessing probability.",
        H("Guessing probability"),
        Blocks(
            Describe.Lean(DescribeId.Create("measurement-total-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.measurement_trace_sum"),
                H("Identity-summing measurements preserve total trace pairing"),
                StatementSource.FromAuthor(MeasurementTraceSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite label and matrix index types, a trace-one complex matrix has total real trace pairing one with any matrix family whose sum is the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurement-success-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.success_bounds"),
                H("Every POVM success probability lies between zero and one"),
                StatementSource.FromAuthor(SuccessBoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite label and matrix index types, nonnegative weights summing to one, density states, and positive semidefinite measurement effects summing to the identity, the success probability lies in the closed unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurement-success-probability"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.successProbability"),
                H("The success probability of a labelled measurement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("For a finite ensemble of density states rho_x with label weights p_x, successProbability is sum_x p_x Re Tr(M_x rho_x). The finite measurement has exactly one output for each guessed label."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("measurement-success-set"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet"),
                H("The genuine POVM success set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("successProbabilitySet consists of exactly the success probabilities of matrices M_x that are positive semidefinite and sum to the identity. No restriction to projective measurements is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("optimal-guessing-probability"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.pGuess"),
                H("The optimal guessing probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("pGuess is the supremum of successProbabilitySet. For nonnegative normalized ensemble weights, pGuess_bounds establishes that the set is nonempty and bounded above, and that 0<pGuess<=1 and 1-pGuess<=-log pGuess. Positivity follows from the deterministic measurement guessing a positive-weight label; normalization itself excludes an empty label type. The same proof establishes that any bound q<=1-successProbability valid for every labelled POVM implies q<=1-pGuess. It requires no attainment theorem for an optimal POVM.")),
                    Paragraph(Text("These probability and supremum statements do not assert a bound on conditional subentropy. That further conclusion requires the separate matrix pinching-gap inequality for every POVM."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guessing-probability-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds"),
                H("Bounded positive guessing probability and supremum transfer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(Paragraph(Text("For every finite nonnegative normalized ensemble, the genuine POVM success set is nonempty and bounded above, and its supremum lies in (0,1]. The logarithmic comparison 1-pGuess<=-log pGuess follows from log p<=p-1. Every bound q<=1-successProbability valid for all finite POVMs transfers to q<=1-pGuess by the defining least-upper-bound property. No optimal measurement or supremum attainment is assumed."))), DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula MeasurementTraceSumFormula()
    {
        Formula xType = F.Id("X");
        Formula bType = F.Id("B");
        Formula r = F.Id("R");
        Formula m = F.Id("M");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", bType, bType, complex);
        Formula summand = Seq(Call("M", F.Id("x")), Sp, r);
        Formula total = Seq(Sum, Underscore, Grp(Seq(F.Id("x"), Sp, InMacro, Sp, xType)),
            Sp, Call("Re", Call("trace", summand)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), F.Id("FiniteType")),
                new Formula.BoundVariable(FormulaIdentifier.Create("B"), F.Id("FiniteType")),
                new Formula.BoundVariable(FormulaIdentifier.Create("R"), matrix),
                new Formula.BoundVariable(FormulaIdentifier.Create("M"), Seq(xType, To, matrix)),
            ],
            Seq(Call("trace", r), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Call("sum", m), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
                total, Sp, Eq, Sp, D(1))));
    }

    private static Formula SuccessBoundsFormula()
    {
        Formula xType = F.Id("X");
        Formula bType = F.Id("B");
        Formula p = F.Id("p");
        Formula rho = F.Id("rho");
        Formula m = F.Id("M");
        Formula x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", bType, bType, complex);
        Formula sumP = Call("sum", p);
        Formula sumM = Call("sum", m);
        Formula allWeights = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), xType)],
            Seq(D(0), Sp, Le, Sp, Call("p", x)));
        Formula allEffects = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"), xType)],
            Call("PosSemidef", Call("M", x)));
        Formula hypotheses = Seq(allWeights, Sp, Land, Sp, sumP, Sp, Eq, Sp, D(1),
            Sp, Land, Sp, allEffects, Sp, Land, Sp, sumM, Sp, Eq, Sp, D(1));
        Formula success = Call("successProbability", p, rho, m);
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), F.Id("FiniteType")),
                new Formula.BoundVariable(FormulaIdentifier.Create("B"), F.Id("FiniteType")),
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), Seq(xType, To, real)),
                new Formula.BoundVariable(FormulaIdentifier.Create("rho"),
                    Seq(xType, To, Call("DensityState", bType))),
                new Formula.BoundVariable(FormulaIdentifier.Create("M"), Seq(xType, To, matrix)),
            ],
            Seq(hypotheses, Sp, Rightarrow, Sp, D(0), Sp, Le, Sp, success,
                Sp, Land, Sp, success, Sp, Le, Sp, D(1))));
    }
}
