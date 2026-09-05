using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArchimedeanTailJetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet.";
    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }
    private static Formula Sq(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));

    public DocumentDefinition Create()
    {
        Formula L = F.Id("L"), t = F.Id("t"), m = F.Id("m");
        Formula N = F.Id("N"), v = F.Id("v"), q = F.Id("q"), rho = F.Id("rho");
        Formula w = Call("w", L, t), response = Call("R", L, t, v);
        Formula jet = Call("P", m, L, t, v);
        Formula exact = Call("D", L, t, v), approx = Call("J", m, L, t, v);
        Formula bound = Seq(Call("abs", w), Sp, D(2), Sp,
            Grp(q), Caret, Grp(m), Sp, Sq(Call("inv", Seq(D(1), Minus, q))), Sp,
            Grp(D(2), Sp, N, Plus, D(1)), Sp, Call("EuclideanMass", v));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A boundary-moment jet controls every even coefficient direction of the "
                + "canonical arithmetic Gamma tail at every order and past-band frequency.",
            H("Weil Archimedean Tail Jet"),
            Blocks(
                Paragraph(Text(
                    "N and m are natural numbers. L is the support length, rho=2*pi/L, "
                    + "and v is an arbitrary complex vector indexed by 0,...,N with ordinary "
                    + "Euclidean mass sum_k |v_k|^2. The weights sigma_0=1 and "
                    + "sigma_k=sqrt(2) for k>0 implement the isometric even embedding. "
                    + "Set x_k=(rho*k/t)^2, q=(rho*N/t)^2, "
                    + "R=sum_k sigma_k*v_k/(1-x_k), "
                    + "P=sum_k sigma_k*v_k*sum_{j<m} x_k^j, and "
                    + "w=(2*rho/pi^2)*Zeta23.EF.gammaBracket(t)*sin(L*t/2)^2/t^2. "
                    + "The compatible physical cosine basis on [-L/2,L/2] has diagonal "
                    + "phase (-1)^k. This phase is part of the convention, not an omitted sign.")),
                Describe.Lean(
                    DescribeId.Create("even-archimedean-tail-density"),
                    DeclarationHandle.Create(Owner + "evenArchimedeanTailDensity"),
                    H("The exact canonical Cauchy density"),
                    StatementSource.FromAuthor(Disp(Seq(exact, Eq, Sp,
                        w, Sp, Sq(Call("norm", response))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The density retains the existing gammaBracket exactly. Its "
                        + "identification with the trigonometric Galerkin tail is the "
                        + "Cauchy-density calculation of Groskin, arXiv:2607.02828, "
                        + "Theorem 3.2; the Fourier-to-density identification is a cited "
                        + "analytic input and is not asserted as a Lean theorem here."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("even-archimedean-jet-density"),
                    DeclarationHandle.Create(Owner + "evenArchimedeanJetDensity"),
                    H("Retain the finite boundary-moment jet"),
                    StatementSource.FromAuthor(Disp(Seq(approx, Eq, Sp,
                        w, Sp, Sq(Call("norm", jet))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite jet is a sum of the even boundary moments of orders "
                        + "0,2,...,2*(m-1). No moment is set to zero. The prime and pole "
                        + "pieces of the complete Weil form are not redefined. "
                        + "The order-zero jet is the empty sum and is included."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("even-archimedean-tail-density-jet-error"),
                    DeclarationHandle.Create(Owner + "even_archimedean_tail_density_jet_error"),
                    H("An all-direction, all-order density error bound"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("Positive", Seq(t, Minus, rho, Sp, N)),
                        Sp, Rightarrow, Sp, Call("abs", Seq(exact, Minus, approx)),
                        Leq, Sp, bound))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Positive(x) means 0<x. The assumptions are exactly L>0 and "
                        + "rho*N<t; they imply 0<=q<1 and include N=0. The conclusion "
                        + "holds for every complex coefficient vector. The proof uses "
                        + "the exact finite geometric remainder, two norm bounds, and "
                        + "sum sigma_k^2=2*N+1 through finite Cauchy-Schwarz. "
                        + "The sign of gammaBracket is not assumed. Even when both "
                        + "densities are positive, their difference need not be positive. "
                        + "Integration, the independent Gamma envelope, and the optimized "
                        + "positive projection correction are separate analytic results "
                        + "in the theory note, not conclusions of this Lean declaration. "
                        + "No complete-window complement gap, ground-state simplicity, "
                        + "or convergence of ground modes to Xi is asserted."))),
                    DescribeRole.Theorem))));
    }
}
