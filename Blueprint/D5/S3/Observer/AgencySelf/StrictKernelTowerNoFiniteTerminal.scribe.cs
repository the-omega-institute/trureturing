using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class StrictKernelTowerNoFiniteTerminalDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencySelf/StrictKernelTowerNoFiniteTerminal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly refining finite interaction profiles have no finite terminal agency-self "
            + "quotient.",
        H("Strict Kernel Tower Has No Finite Terminal Self"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-kernel-tower-has-no-finite-terminal-self"),
                DeclarationHandle.Create(Prefix + "strict_kernel_tower_no_finite_terminal"),
                H("No finite interaction stage is terminal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A level-indexed interaction profile maps each history to a probability "
                            + "law for every intervention available at that level. The complete "
                            + "profile is the canonical dependent joint readout of all finite "
                            + "profiles.")),
                    Paragraph(Text(
                        "Assume every successor profile has an equality kernel strictly contained "
                            + "in its predecessor's kernel. No finite quotient then admits an "
                            + "equivalence to the complete-profile quotient that sends every "
                            + "history class to the class of the same representative.")),
                    Paragraph(Text(
                        "The representative law is public because a bare equivalence of carrier "
                            + "types does not identify quotient kernels. Strict descent also gives, "
                            + "at every finite level, two histories that the current profile "
                            + "identifies and the successor profile separates."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula history = F.Id("H");
        Formula intervention = F.Id("I");
        Formula interaction = F.Id("O");
        Formula profile = F.Id("Gamma");
        Formula level = F.Id("n");
        Formula next = Seq(level, Plus, D(1));
        Formula left = F.Id("h");
        Formula right = F.Id("hPrime");
        Formula equivalence = F.Id("E");

        Formula InterventionAt(Formula index) =>
            Call("I", index);

        Formula ProfileAt(Formula index) =>
            Call("Gamma", index);

        Formula ProfileValue(Formula index, Formula value) =>
            Call("Gamma", index, value);

        Formula KernelAt(Formula index) =>
            Call("ker", ProfileAt(index));

        Formula fullProfile = Call("jointReadout", profile);
        Formula fullKernel = Call("ker", fullProfile);
        Formula finiteKernel = KernelAt(level);
        Formula finiteQuotient = Call("Quotient", finiteKernel);
        Formula fullQuotient = Call("Quotient", fullKernel);
        Formula profileType = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            Arrow(
                history,
                Arrow(InterventionAt(level), Call("PMF", interaction))));

        Formula strictDescent = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            Call("StrictSubset", KernelAt(next), KernelAt(level)));

        Formula preservesRepresentatives = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("h", history)],
            Equal(
                Call("E", Call("quotientClass", finiteKernel, left)),
                Call("quotientClass", fullKernel, left)));
        Formula canonicalEquivalence = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("E", Call("Equiv", finiteQuotient, fullQuotient))],
            preservesRepresentatives);
        Formula noFiniteTerminal = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            new Formula.Not(canonicalEquivalence));

        Formula separatingPair = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("h", history), Bound("hPrime", history)],
                And(
                    Equal(ProfileValue(level, left), ProfileValue(level, right)),
                    NotEqual(ProfileValue(next, left), ProfileValue(next, right)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("H", type),
                Bound("I", Arrow(naturals, type)),
                Bound("O", type),
                Bound("Gamma", profileType),
            ],
            Implies(strictDescent, And(noFiniteTerminal, separatingPair))));
    }
}
