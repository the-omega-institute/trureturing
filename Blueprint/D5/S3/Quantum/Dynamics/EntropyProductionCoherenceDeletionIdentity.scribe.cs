using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class EntropyProductionCoherenceDeletionIdentityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary evolution followed by coordinate-basis pinching produces entropy equal "
            + "to the deleted coherence, with nonnegative gains that telescope.",
        H("Entropy Production by Coherence Deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entropy-production-coherence-deletion-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity."
                        + "entropy_production_coherence_deletion_identity"),
                H("Entropy production equals deleted coherence"),
                StatementSource.FromAuthor(IdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a unitary complex matrix on a finite decidable carrier. "
                            + "Starting from a sequence of density states, assume each next "
                            + "state is obtained by conjugating with U and then deleting the "
                            + "off-diagonal entries in the fixed coordinate basis.")),
                    Paragraph(Text(
                        "At every step, the entropy gain is exactly the quantum relative "
                            + "entropy from the evolved state to its pinched state, and this "
                            + "quantity is nonnegative. Summing these one-step identities "
                            + "gives the finite-horizon entropy balance."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula IdentityFormula()
    {
        Formula carrier = F.Id("n"), unitary = F.Id("U"), sequence = Rho;
        Formula step = F.Id("k"), horizon = F.Id("N");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula carrierType = Seq(Operatorname, Grp(F.Id("Type")));
        Formula matrixType = Call("Matrix", carrier, carrier, complex);
        Formula densityType = Call("DensityState", carrier);
        Formula sequenceType = Seq(natural, Sp, Mapsto, Sp, densityType);

        Formula StateAt(Formula index) => Sub(sequence, index);
        Formula EvolvedAt(Formula index) =>
            Call("unitaryConjugateState", unitary, StateAt(index));
        Formula PinchedAt(Formula index) =>
            Call("basisPinchingState", EvolvedAt(index));
        Formula TaxAt(Formula index) =>
            Call("quantumRelativeEntropy", EvolvedAt(index), PinchedAt(index));
        Formula EntropyAt(Formula index) =>
            Call("vonNeumannEntropy", StateAt(index));

        Formula nextStep = Seq(step, Plus, D(1));
        Formula recurrence = Seq(
            Forall, Sp, step, Sp, InMacro, Sp, natural, Comma, Sp,
            StateAt(nextStep), Sp, Eq, Sp, PinchedAt(step));
        Formula oneStep = Seq(
            Forall, Sp, step, Sp, InMacro, Sp, natural, Comma, Sp,
            Open,
            EntropyAt(nextStep), Sp, Minus, Sp, EntropyAt(step), Sp, Eq, Sp,
            TaxAt(step),
            Sp, Land, Sp, D(0), Sp, Leq, Sp, TaxAt(step),
            Close);
        Formula totalTax = Seq(
            Sum, Underscore, Grp(step, Sp, Lt, Sp, horizon), Sp, TaxAt(step));
        Formula telescope = Seq(
            Forall, Sp, horizon, Sp, InMacro, Sp, natural, Comma, Sp,
            EntropyAt(horizon), Sp, Minus, Sp, EntropyAt(D(0)), Sp, Eq, Sp,
            totalTax);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Colon, Sp, carrierType, Comma, Sp,
            unitary, Colon, Sp, matrixType, Comma, Sp,
            sequence, Colon, Sp, sequenceType, Comma, RowBreak, Grp(),
            Call("Fintype", carrier), Sp, Land, Sp,
            Call("DecidableEq", carrier), Sp, Land, Sp,
            unitary, Sp, InMacro, Sp, Call("unitaryGroup", carrier, complex), Sp,
            Land, RowBreak, Grp(),
            recurrence, Sp, Rightarrow, RowBreak, Grp(),
            Open, oneStep, Close, Sp, Land, RowBreak, Grp(),
            Open, telescope, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
