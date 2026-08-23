using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class FutureProbabilityResidualCorrelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula a = F.Id("a");
        Formula rho = Rho;
        Formula heisenberg = F.Id("H");
        Formula effects = F.Id("E");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula carrier = Call("HermitianTraceZero", d);
        Formula matrix = Call("Matrix", d, d, complexes);
        Formula effectIndex = Call("Fin", Seq(r, Plus, D(1)));
        Formula visible = F.Id("S");
        Formula residual = F.Id("R");
        Formula state = Seq(F.Id("X"), Underscore, Grp(rho));
        Formula future = Seq(F.Id("A"), Underscore, Grp(a, Comma, k));
        Formula representative = Seq(rho, Underscore, Grp(m));
        Formula error = Seq(Delta, Sp, F.Id("p"), Underscore, Grp(a, Comma, k),
            Caret, Grp(Open, m, Close));
        Formula visibleDefinition = Call("towerSpace", heisenberg, effects, m);
        Formula residualDefinition = new Formula.Power(visible, Grp(Perp));
        Formula stateDefinition = Call("densityCoordinate", rho);
        Formula futureDefinition = Seq(
            new Formula.Power(heisenberg, Grp(k)),
            Open, effects, Open, a, Close, Close);
        Formula representativeDefinition =
            Call("linearPredictionRepresentative", visible, state);
        Formula errorDefinition = Call("ReTr", Seq(
            Open, rho, Minus, representative, Close, future));
        Formula stateResidual = Call("P", residual, state);
        Formula futureResidual = Call("P", residual, future);
        Formula exactCorrelation = Seq(
            error, Sp, Eq, Sp, Call("innerHS", stateResidual, futureResidual));
        Formula residualBound = Seq(
            Call("abs", error), Sp, Leq, Sp,
            Sqrt, Grp(Call("residualMass", visible, state)), Sp,
            Call("normHS", futureResidual));
        Formula witnessDensity = Call("diag", D(1), D(0), D(0));
        Formula witnessDirection = Call("diag", D(1), D(0), Seq(Minus, D(1)));
        Formula witnessVisible = Call("span", reals, witnessDirection);
        Formula witnessRepresentative = Call(
            "linearPredictionRepresentative",
            witnessVisible,
            Call("densityCoordinate", witnessDensity));
        Formula nonpositiveWitness = Seq(
            Neg, Call("PosSemidef", witnessRepresentative));
        Formula statement = Disp(Seq(
            Forall, Sp, d, Comma, Sp,
            OpenBracket, Call("Fintype", d), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", d), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", d), CloseBracket, Comma,
            RowBreak, Grp(), rho, Colon, Sp, matrix, Comma, Sp,
            heisenberg, Colon, Sp, Call("LinearMap", reals, carrier, carrier), Comma,
            RowBreak, Grp(), r, InMacro, Sp, naturals, Comma, Sp,
            effects, Colon, Sp, effectIndex, Sp, To, Sp, carrier,
            Comma, Sp, m, Comma, Sp, k, InMacro, Sp, naturals,
            Comma, Sp, a, InMacro, Sp, effectIndex, Comma,
            RowBreak, Grp(), Call("Density", rho), Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            visible, Sp, Eq, Sp, visibleDefinition, Comma, Sp,
            residual, Sp, Eq, Sp, residualDefinition, Comma,
            RowBreak, Grp(), state, Sp, Eq, Sp, stateDefinition, Comma, Sp,
            future, Sp, Eq, Sp, futureDefinition, Comma,
            RowBreak, Grp(), representative, Sp, Eq, Sp,
            representativeDefinition, Comma, Sp,
            error, Sp, Eq, Sp, errorDefinition, SemiSpace,
            RowBreak, Grp(), exactCorrelation, Sp, Land, Sp,
            RowBreak, Grp(), residualBound, Sp, Land, Sp,
            RowBreak, Grp(), nonpositiveWitness, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Future linear-prediction error is exactly the correlation of state and effect residuals.",
            H("Future Probability Residual Correlation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("future-probability-residual-correlation"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation."
                            + "future_probability_residual_correlation"),
                    H("Future probability error is the exact residual correlation"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let rho be a positive semidefinite trace-one matrix on a finite "
                                + "nonempty carrier. Its centered coordinate lies in the canonical "
                                + "real trace-zero Hermitian space. A real-linear Heisenberg map "
                                + "and a finite centered-effect family construct the visible tower "
                                + "S, its orthogonal residual R, and every future effect A_a,k.")),
                        Paragraph(Text(
                            "The linear representative retains the visible projection of the "
                                + "centered state and restores the trace-one identity component. "
                                + "The real trace error against every iterated future effect equals "
                                + "the Hilbert--Schmidt inner product of the state and effect "
                                + "residual projections.")),
                        Paragraph(Text(
                            "Cauchy--Schwarz bounds the absolute error by the square root of the "
                                + "canonical residual mass times the future effect residual norm. "
                                + "The final public conjunct uses the valid density diag(1,0,0) "
                                + "and the visible real line spanned by diag(1,0,-1); its projected "
                                + "representative has diagonal entries 5/6, 1/3, and -1/6, so it "
                                + "is not positive semidefinite.")),
                        Paragraph(Text(
                            "The proof applies the exact orthogonal-projection self-adjointness "
                                + "and Cauchy--Schwarz bounds from the pinned library. Repository "
                                + "carrier, tower, residual-space, residual-mass, and centered-state "
                                + "definitions are imported rather than redeclared."))),
                    DescribeRole.Theorem))));
    }
}
