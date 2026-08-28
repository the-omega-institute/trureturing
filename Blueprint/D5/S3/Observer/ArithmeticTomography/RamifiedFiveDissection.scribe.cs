using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class RamifiedFiveDissectionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six observable states arise from five ordinary residues and one ramification residual.",
        H("Six-State Ramified Five-Dissection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("six-state-ramified-five-dissection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "six_state_ramified_five_dissection"),
                H("Five residues acquire one additional isotropic residual channel"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state carrier is built from five ordinary residue labels and a "
                            + "separate ramificationResidual label, so its cardinality is exactly "
                            + "6 = 5 + 1. For every nonzero energy residue, the observer label is "
                            + "the residue n mod 5.")),
                    Paragraph(Text(
                        "At zero residue, the supplied source witnesses distinguish a zero "
                            + "boundary from a nonzero boundary. The energy-boundary congruence "
                            + "forces the latter boundary to be q_R-isotropic, and the two labels "
                            + "are unequal.")),
                    Paragraph(Text(
                        "The residual constructor is outside the range of ordinary labels. This "
                            + "is the extra first-order jet channel left by the ramified prime 5; "
                            + "the theorem assumes the source lattice data and does not replace it "
                            + "with an enumerated Fin carrier."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula data = F.Id("D");
        Formula x = F.Id("x");
        Formula energy = Call("energy", data, x);
        Formula residue = Call("ordinaryResidue", energy);
        Formula state = Call("stateOf", data, x);
        Formula zeroState = Call("stateOf", data, Call("zeroWitness", data));
        Formula residualState = Call("stateOf", data, Call("residualWitness", data));
        Formula rhoZero = Call("rho5", data, Call("zeroWitness", data));
        Formula rhoResidual = Call("rho5", data, Call("residualWitness", data));
        Formula qResidual = Call("qR", rhoResidual);
        Formula ordinary = Call("ordinary", residue);
        Formula residual = F.Id("ramificationResidual");
        Formula ordinaryLabels = Call("range", F.Id("ordinary"));
        Formula residualOutsideOrdinary = new Formula.Not(
            new Formula.Relation(
                residual,
                FormulaRelationOperator.MemberOf,
                ordinaryLabels));

        return Disp(Seq(
            D(6), Sp, Eq, Sp, D(5), Plus, Sp, D(1), Sp, Land, Sp,
            Open, Forall, Sp, x, Sp, InMacro, Sp, Call("L", data), Comma, Sp,
            new Formula.Modulo(energy, D(5)), Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, state, Sp, Eq, Sp, ordinary, Close, Sp, Land, Sp,
            rhoZero, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            rhoResidual, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            qResidual, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            zeroState, Sp, Neq, Sp, residualState, Sp, Land, Sp,
            residualOutsideOrdinary, Dot));
    }
}
