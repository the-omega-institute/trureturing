using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class RamifiedFiveDissectionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed Lambda-square A4 lattice realizes five residue states and one ramified jet state.",
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
                        "ExteriorSquareA4 is the source's six-integer coordinate lattice with its "
                            + "displayed Gram matrix G. The boundary map uses the displayed fixed "
                            + "matrix R_5, and q_R uses the displayed matrix H. The first conjunct "
                            + "equates the cardinality of the actual stateOf image with the "
                            + "RamifiedFiveState carrier; ramified_state_card computes that carrier "
                            + "as the five ordinary constructors plus one residual constructor. "
                            + "For nonzero energy residue, stateOf returns that residue.")),
                    Paragraph(Text(
                        "The theorem uses fixed lattice points, not caller-supplied witnesses. The "
                            + "zero point has zero R_5 boundary. The fixed residual point has "
                            + "a nonzero q_R-isotropic boundary, and stateOf assigns the two points "
                            + "different labels.")),
                    Paragraph(Text(
                        "RamifiedFiveRoot carries the repository theorem 5 = (-1 + 2 phi)^2. Its "
                            + "class in the named first-order neighborhood GoldenInt/(5) is the "
                            + "residual jet. Ordinary state observations are zero in this quotient, "
                            + "while the final non-membership says the residual jet observation is "
                            + "not among them."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula x = F.Id("x");
        Formula r = F.Id("r");
        Formula energy = Call("energyResidue", x);
        Formula residue = Call("ordinaryResidue", x);
        Formula state = Call("stateOf", x);
        Formula zeroState = Call("stateOf", F.Id("zeroWitness"));
        Formula residualState = Call("stateOf", F.Id("residualWitness"));
        Formula rhoZero = Call("rho5", F.Id("zeroWitness"));
        Formula rhoResidual = Call("rho5", F.Id("residualWitness"));
        Formula qResidual = Call("qR", rhoResidual);
        Formula ordinary = Call("ordinary", residue);
        Formula ordinaryJetMap = Seq(
            Open, r, Sp, Mapsto, Sp,
            Call("firstOrderJetObservation", Call("ordinary", r)), Close);
        Formula residual = F.Id("ramificationResidual");
        Formula stateRangeCard = Call("ncard", Call("range", F.Id("stateOf")));
        Formula stateCarrierCard = Call("card", F.Id("RamifiedFiveState"));
        Formula residualJet = Call("firstOrderJetObservation", residual);
        Formula ordinaryJetRange = Call("range", ordinaryJetMap);
        Formula residualJetOutsideOrdinary = new Formula.Not(
            new Formula.Relation(
                residualJet,
                FormulaRelationOperator.MemberOf,
                ordinaryJetRange));

        return Disp(Seq(
            stateRangeCard, Sp, Eq, Sp, stateCarrierCard, Sp, Land, Sp,
            Open, Forall, Sp, x, Sp, InMacro, Sp, F.Id("ExteriorSquareA4"), Comma, Sp,
            energy, Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, state, Sp, Eq, Sp, ordinary, Close, Sp, Land, Sp,
            rhoZero, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            rhoResidual, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            qResidual, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            zeroState, Sp, Neq, Sp, residualState, Sp, Land, Sp,
            residualJetOutsideOrdinary, Dot));
    }
}
