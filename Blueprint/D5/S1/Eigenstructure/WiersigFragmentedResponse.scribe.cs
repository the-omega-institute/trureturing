using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class WiersigFragmentedResponseDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/wiersig2026fragmentedresponse");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp linewidth bound and minimum loss rank for each fragmented Jordan partition.",
        H("Passive fragmented response"),
        TheoremBlocks()));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula BasisVector(Formula position) =>
        Seq(F.Id("B"), Underscore, Grp(F.Id("j"), Comma, position));

    private static Formula Quantify(Formula quantifier, Formula variable, Formula domain, Formula body) =>
        Seq(quantifier, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static BlockSequence TheoremBlocks()
    {
        Formula b = F.Id("b"), p = F.Id("p"), m = F.Id("m"), e = F.Id("E");
        Formula h = F.Id("H"), w = F.Id("W"), j = F.Id("j"), z = F.Id("z"), k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula blocks = Seq(Mathrm, Grp(F.Id("Fin")), Open, b, Close);
        Formula size = Seq(m, Underscore, Grp(j));
        Formula admissible = Seq(Mathcal, Grp(F.Id("A")), Open, e, Comma, m, Close);
        Formula top = Seq(p, Minus, D(1));
        Formula bound = Power(Beta, top);
        Formula n = Seq(F.Id("N"), Underscore, Grp(h));
        Formula nw = Seq(F.Id("N"), Underscore, Grp(w));
        Formula lossRankH = Seq(Operatorname, Grp(F.Id("rank")), Gamma, Open, h, Close);
        Formula lossRankW = Seq(Operatorname, Grp(F.Id("rank")), Gamma, Open, w, Close);
        Formula pencil = Seq(z, F.Id("I"), Minus, h);
        Formula resolvent = Seq(Sum, Underscore, Grp(k, Eq, D(0)), Caret, Grp(top),
            Frac, Grp(Power(n, k)), Grp(Power(Seq(Open, z, Minus, e, Close), Seq(k, Plus, D(1)))));

        Formula response = Call("Response", h);
        Formula attains = Call("Attains", w);
        Formula statement = new Formula.Logic(
            Seq(Open, Quantify(Forall, h, admissible, response), Close),
            FormulaLogicOperator.And,
            Seq(Open, Quantify(Exists, w, admissible, attains), Close));
        Formula assumptions = Seq(D(2), Le, Sp, b, Land, Sp, D(2), Le, Sp, p, Land, Sp, Beta, Gt, Sp, D(0),
            Land, Sp, Open, Quantify(Forall, j, blocks, Seq(size, Le, Sp, p)), Close,
            Land, Sp, Open, Quantify(Exists, j, blocks, Seq(size, Eq, p)), Close);
        Formula responseBounds = Seq(Power(n, top), Neq, Sp, D(0), Land, Sp,
            new Formula.Norm(Power(n, top)), Le, Sp, bound, Land, Sp, lossRankH, Ge, Sp, b);
        Formula spectrum = Quantify(Forall, z, complexes,
            Seq(Neg, Sp, Operatorname, Grp(F.Id("IsUnit")), Open, pencil, Close,
                Leftrightarrow, Sp, z, Eq, e));
        Formula resolventIdentity = Quantify(Forall, z, complexes,
            Seq(z, Neq, Sp, e, Rightarrow, Sp, Power(Seq(Open, pencil, Close), Seq(Minus, D(1))), Eq,
                resolvent));
        Formula attainment = Seq(new Formula.Norm(Power(nw, top)), Eq, bound, Land, Sp, lossRankW, Eq, b);

        var theorem = Describe.Lean(
            DescribeId.Create("sharp-passive-fragmented-response"),
            DeclarationHandle.Create(Handle),
            H("Sharp response and simultaneous minimum loss rank"),
            StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "The closing paragraph of Wiersig's Section VIII (Conclusion) asks whether the passive "
                    + "response bound and rank-one optimality extend to fragmented exceptional "
                    + "points. The resolution here concerns a collision at a sole eigenvalue E "
                    + "with strictly positive linewidth, two or more blocks, and a largest "
                    + "block of size at least two.")),
                Paragraph(Text(
                    "The entire partition is prescribed by a positive size function m on Fin(b). "
                    + "Write m_j for m(j). The largest size p "
                    + "bounds every size and occurs among them. Positions(m) is the dependent sum "
                    + "of Fin(m(j)) over the block labels j. The complex matrices use orthonormal "
                    + "coordinates indexed by Positions(m).")),
                Paragraph(Text(
                    "Write N_H = H − EI, β = −2 Im E, and Γ(H) = i(H − H*), "
                    + "where * denotes conjugate transpose. The matrix norm is the Euclidean operator norm, "
                    + "and rank is over the complex numbers. The admissible class 𝒜(E,m) consists of complex "
                    + "square matrices on Positions(m) with positive semidefinite Γ(H) and a complex linear "
                    + "basis B of the entire coordinate space indexed by Positions(m). For every natural r, "
                    + "every block label j, and every position a in Fin(m(j)), the basis satisfies "),
                    Math(In(Seq(Power(Seq(F.Id("N"), Underscore, Grp(F.Id("H"))), F.Id("r")), Sp,
                        BasisVector(F.Id("a")), Sp, Eq, Sp, BasisVector(Seq(F.Id("a"), Plus, F.Id("r")))))),
                    Text(" when a+r < m(j), and "),
                    Math(In(Seq(Power(Seq(F.Id("N"), Underscore, Grp(F.Id("H"))), F.Id("r")), Sp,
                        BasisVector(F.Id("a")), Sp, Eq, Sp, D(0)))),
                    Text(" otherwise.")),
                Paragraph(Text("For an admissible H, "), Math(response),
                    Text(" holds exactly when all three displays below hold.")),
                new DocumentBlock.DisplayFormula(responseBounds),
                new DocumentBlock.DisplayFormula(spectrum),
                new DocumentBlock.DisplayFormula(resolventIdentity),
                Paragraph(Text("For an admissible W, "), Math(attains),
                    Text(" holds exactly when both equalities below hold for that same W.")),
                new DocumentBlock.DisplayFormula(attainment),
                Paragraph(Text(
                    "For every passive matrix of the given partition, E is the sole eigenvalue. "
                    + "The resolvent is the finite Laurent sum away from E and its highest-order "
                    + "coefficient N^(p−1) is "
                    + "nonzero. The coefficient norm is at most the linewidth to power p−1 "
                    + "and the loss rank is at least b. One matrix of the same partition "
                    + "attains both bounds. In particular the minimum feasible loss rank is b, "
                    + "which makes rank-one loss infeasible in this fragmented setting.")),
                Paragraph(Text(
                    "The normalized Cayley transform gives the norm bound. Restricting the loss "
                    + "to the eigenspace gives an injective map. For attainment use the "
                    + "orthogonal sum S of lower unit shifts and A = (I−S)^−1 − I. Each normalized "
                    + "loss block is the all-ones matrix. The largest block supplies a unit "
                    + "vector on which A^(p−1) has norm one. Ranks of powers give the "
                    + "prescribed chain multiplicities, and the nilpotent Jordan-chain theorem "
                    + "gives a basis with those sizes.")),
                Paragraph(Text(
                    "Collisions embedded in a spectrum with spectator eigenvalues and the "
                    + "physical response measured by the Frobenius norm are outside this theorem's scope."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("wiersig-2026-passive-fragmented-response"),
                ResolutionKind.Proved));

        return Blocks(
            Paragraph(Text("For every "), Math(Seq(b, Comma, p, InMacro, Sp, naturals)),
                Text(", "), Math(Seq(m, Colon, blocks, To, Sp, Seq(naturals, Underscore, Grp(Gt, Sp, D(0))))),
                Text(", and "), Math(Seq(e, InMacro, Sp, complexes)),
                Text(", the theorem below holds under the following assumptions, with "),
                Math(Seq(Beta, Eq, Minus, D(2), Operatorname, Grp(F.Id("Im")), Sp, e)),
                Text(".")),
            new DocumentBlock.DisplayFormula(assumptions),
            theorem);
    }
}
