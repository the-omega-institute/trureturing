using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.OptimalRecovery;

internal sealed class PointwiseMinimaxUpperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite atomic probability laws admit a deterministic ground-energy estimator with a uniform dimension and precision rate.",
        H("Pointwise minimax upper bounds for ground energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-atomiclaw"),
                DeclarationHandle.Create(Prefix + "AtomicLaw"),
                H("The original measure class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real Elo, Ehi, eta, natural d, Borel measure mu and ground g, AtomicLaw means mu is a probability measure, mu({g}) >= ofReal(eta), and its actual topological support equals a finite set s with card(s) <= d, g in s, and every support point x in [Elo,Ehi] with g <= x. Repeated atomic labels are represented by their combined measure mass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-measurecurve"),
                DeclarationHandle.Create(Prefix + "measureCurve"),
                H("Measure-valued Laplace observations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Borel measure mu and real time t, measureCurve(mu,t) is the Bochner integral of exp(-t x) against mu."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-rateall"),
                DeclarationHandle.Create(Prefix + "rateAll"),
                H("The joint dimension and precision rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d and real epsilon, rateAll is the supremum over integers 1 <= m <= d of epsilon^(1/(2m-1))/m^2, using real powers. In the theorems d >= 1 and epsilon > 0, so this is the maximum of a nonempty finite family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-ratewindow"),
                DeclarationHandle.Create(Prefix + "rateWindow"),
                H("The window rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d and real epsilon and U, rateWindow is the supremum over 1 <= m <= d of min(1,epsilon^(1/(2m-1))*max(1,(2m-1)/U))/m^2. The minimax theorem uses U=Ehi*T > 0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-minimaxrisk"),
                DeclarationHandle.Create(Prefix + "minimaxRisk"),
                H("Deterministic pointwise minimax risk"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/micchellirivlin1977optimalrecovery")),
                Blocks(Paragraph(Text("For every parameter tuple Elo,Ehi,eta,d,D,epsilon, minimaxRisk is the infimum over all estimators G:(D -> real)->real of the supremum of ofReal(|G(Y)-g|), over every AtomicLaw mu,g and every arbitrary observation function Y on D with |Y(t)-measureCurve(mu,t)| <= epsilon at each t. The risk uses extended nonnegative reals. No continuity, stochastic noise law or computational restriction is imposed on Y or G."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-atomic-law-representation"),
                DeclarationHandle.Create(Prefix + "atomic_law_representation"),
                H("Exact finite reconstruction of the measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every AtomicLaw has g in [Elo,Ehi] and a nonnegative finitely supported real weight function w of total mass 1, supported in [g,Ehi], with w(g) >= eta and at most d support points. The original measure equals sum_x ofReal(w(x)) dirac(x), and for every real t its measureCurve equals atomicLaplace(w,t). This is an exact representation, including support collisions and all times."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-compatiblegrounds"),
                DeclarationHandle.Create(Prefix + "compatibleGrounds"),
                H("Ground energies compatible with one observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every observation Y on D, compatibleGrounds is the set of all g for which some AtomicLaw mu,g obeys the pointwise epsilon noise constraint for that same Y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-midpointestimator"),
                DeclarationHandle.Create(Prefix + "midpointEstimator"),
                H("The midpoint of the compatible grounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/micchellirivlin1977optimalrecovery")),
                Blocks(Paragraph(Text("The estimator assigns Y the midpoint of the infimum and supremum of compatibleGrounds, with value Elo when that set is empty. For every feasible Y the set is nonempty and bounded by [Elo,Ehi]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-exists-window-estimator"),
                DeclarationHandle.Create(Prefix + "exists_window_estimator"),
                H("One estimator works for every feasible law and observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/micchellirivlin1977optimalrecovery")),
                Blocks(Paragraph(Text("For every 0 <= Elo < E, 0 < eta < 1, d >= 1, T > 0 and epsilon > 0, there exists one estimator G on arbitrary functions on [0,T] such that for every AtomicLaw mu,g and every pointwise epsilon-accurate observation Y, |G(Y)-g| <= (1024E/eta^2) rateWindow(d,epsilon,E*T). The midpoint estimator supplies this common choice; the joint Laplace certificate bounds the diameter of its compatible set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-minimax-window-upper"),
                DeclarationHandle.Create(Prefix + "minimax_window_upper"),
                H("A uniform finite-window minimax upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/micchellirivlin1977optimalrecovery")),
                Blocks(Paragraph(Text("For every 0 <= Elo < E, 0 < eta < 1, d >= 1, T > 0 and epsilon > 0, minimaxRisk on [0,T] is at most ofReal((1024E/eta^2) rateWindow(d,epsilon,E*T)). The constant is independent of d and T. This holds also when E*T < 1 and epsilon >= 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optimalrecovery-pointwiseminimaxupper-minimax-all-upper"),
                DeclarationHandle.Create(Prefix + "minimax_all_upper"),
                H("A uniform all-time minimax upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/micchellirivlin1977optimalrecovery")),
                Blocks(Paragraph(Text("For every 0 <= Elo < E, 0 < eta < 1, d >= 1 and epsilon > 0, minimaxRisk on all t >= 0 is at most ofReal((1024E/eta^2) rateAll(d,epsilon)). In particular the dimension-precision matching upper-bound question holds for all 0 < epsilon < 1 with epsilon0=1. The result concerns finite atomic probability laws with a prescribed ground mass; it makes no bound for an unrestricted positive residual tail."))),
                DescribeRole.Theorem))));
}
