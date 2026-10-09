using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class EffectiveRationalTransportTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual historical survivor transport and a rational certificate independent of the target law.",
        H("Historical Survivor Transport and Rational Search"),
        Blocks(
            Paragraph(Text(
                "Histories are complete finite words over an actual finite alphabet. "
                + "NormalizedRows means nonnegative rows summing to one. The trajectoryLaw begins "
                + "at the empty-history row and thereafter reads its own observed full prefix. "
                + "wordCylinder fixes precisely the coordinates of its finite word. deletedSet "
                + "is the union of these cylinders, and its complement is the final survivor event. "
                + "Legal means prefix freedom, exclusion of the empty word and the prescribed "
                + "cardinality bound at every depth. The target law may be noncomputable.")),
            Describe.Lean(
                DescribeId.Create("historical-survivor-transport"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail.historical_survivor_transport"),
                H("Finite clopen comparison with the second original law's tail"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write r = 1 - (card(A)-1) delta and rho = a r. The row comparison is "
                        + "a comparison of entries at the same actual history. Only the second law "
                        + "needs the common lower bound delta. Its normalization then bounds each "
                        + "entry above by r. Both laws are the actual normalized trajectory measures.")),
                    Paragraph(Text(
                        "At depth N, take all words without a forbidden ancestor of length at most N. "
                        + "Their cylinders are disjoint and their union is exactly the finite survivor "
                        + "clopen. The row comparison bounds each of those cylinder masses by c to "
                        + "the power N times its mass under the second law. Group the remaining "
                        + "forbidden words by their actual lengths N+1+k. The budget and the path "
                        + "bound give a geometric majorant rho to the power N+1+k under that same "
                        + "second law. Subadditivity and summation supply its original-law tail.")),
                    Paragraph(Text(
                        "The finite survivor is contained in the union of the final survivor and "
                        + "the remaining deletion event. Combining these two comparisons gives the "
                        + "displayed full-law inequality. The proof assumes neither infinite-law "
                        + "absolute continuity nor a positive survivor gap. Horizon zero, empty codes "
                        + "and zero budgets are included. The inequality itself does not require "
                        + "c rho to be less than one; that extra condition is used by the searches."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-free-historical-rational-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/EffectiveRationalTransportTail.q_free_historical_rational_certificate"),
                H("General-budget and one-word rational certificates"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite alphabet is represented by Fin(d) with its full discrete "
                        + "measurable structure. Runtime inputs are the natural d, positive rational "
                        + "delta at most 1/d, and total functions b and nu supplied by executable "
                        + "programs. The modulus contract is that b(n) is at most t to the power n "
                        + "whenever rational t is greater than one and n is at least nu(t). "
                        + "The Boolean oneWord selects the general branch when false. B is the real "
                        + "sum of b(n+1)/d to the power n+1. Strict B less than one "
                        + "is a promise, not a decision test.")),
                    Paragraph(Text(
                        "In the general branch choose r = 1-(d-1)delta, a = (1+1/r)/2, rho = a r, "
                        + "c = (1+1/rho)/2 and J = floor(1/((c-1)delta))+1. These are exact "
                        + "rational operations and a natural floor. They satisfy a,c greater than "
                        + "one, rho and c rho less than one, and 1+1/(J delta) less than c.")),
                    Paragraph(Text(
                        "The initial search tests N at least nu(a) and "
                        + "B(N)+(a/d) to the power N+1 divided by (1-a/d) less than one, "
                        + "where B(N) is the finite budget sum. The positive complement is gamma(0). "
                        + "Each of J subsequent steps searches N at least max(1,nu(a)) until "
                        + "rho(c rho) to the power N divided by (1-rho) is less than gamma/2, "
                        + "then replaces gamma by gamma divided by 2 c to the power N. "
                        + "Nat.find carries out these decidable exact rational searches; its "
                        + "existence proofs are erased from execution.")),
                    Paragraph(Text(
                        "The initial upper bounds converge to B and bound it above, so the "
                        + "strict promise terminates the first search. Geometric decay terminates "
                        + "each later search. For the proof, interpolate the rows by "
                        + "Q(j,v,z)=(1-j/J)/d+(j/J)q(v,z). Their normalization, lower bounds "
                        + "and successive row ratios are derived from the original row hypotheses. "
                        + "Induction using actual survivor transport reaches Q(J)=q. The frozen "
                        + "attained extremum converts the universal survivor bound to historicalGap.")),
                    Paragraph(Text(
                        "In both branches the returned rational is strictly positive and at most the joint "
                        + "historical gap. No q, forbidden code, probability-name oracle or "
                        + "positive-gap assumption enters its runtime input. The input functions "
                        + "are executable higher-order Lean values; this declaration does not "
                        + "supply an encoding of arbitrary machine indices or a separate Partrec "
                        + "index theorem. It asserts no speed bound or decision outside the promise.")),
                    Paragraph(Text(
                        "The true branch retains the one-word construction of theorem 5.3.2 in "
                        + "the same certificate definition. Its contract requires d at least three "
                        + "and b(n)=1. Put delta=ell; the source inputs have 0<ell<1/d and "
                        + "ell<p(z) at every coordinate, with p summing to one. The formal "
                        + "construction also permits ell=1/d when only the non-strict historical "
                        + "conclusion is requested. This branch sets a=1, rho=r and c=1+ell, "
                        + "so c rho=1-(d-2)ell-(d-1)ell squared is less than one. Its same floor "
                        + "choice of J is greater than ell to the power minus two. Initial gamma "
                        + "is exactly (d-2)/(d-1). Each depth search starts at one and uses "
                        + "r(rc) to the power N divided by 1-r. The recurrence is unchanged "
                        + "and the output is exactly gamma(J)/2. This path does not query b "
                        + "or nu; they can be fixed to the constant programs one and zero.")),
                    Paragraph(Text(
                        "For iid p with all coordinates greater than ell, prefix freedom makes "
                        + "the actual deleted cylinders disjoint. The frozen exact cylinder law "
                        + "identifies their sum with codeMass(p,F). The frozen iid optimizer "
                        + "attains its supremum. Thus the halved output is strictly less than "
                        + "eta(p), defined as one minus the supremum of real code masses over "
                        + "Legal(constant one,F). The proof uses the original target iid law; "
                        + "its interpolation is confined to the erased soundness proof."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula TransportFormula()
    {
        Formula alpha = F.Id("A"), list = Call("List", alpha), real = Call("Real");
        Formula qzero = Sub(F.Id("q"), D(0)), qone = Sub(F.Id("q"), D(1));
        Formula hzero = Sub(F.Id("h"), D(0)), hone = Sub(F.Id("h"), D(1));
        Formula delta = DeltaLower, c = F.Id("c"), a = F.Id("a"), n = F.Id("N");
        Formula b = F.Id("b"), code = F.Id("F"), z = F.Id("z"), v = F.Id("v");
        Formula r = Seq(D(1), Sp, Minus, Sp,
            Open, Call("card", alpha), Sp, Minus, Sp, D(1), Close, Sp, delta);
        Formula rho = Seq(a, Sp, Open, r, Close);
        Formula rows = Seq(list, Sp, To, Sp, alpha, Sp, To, Sp, real);
        Formula lower = All(v, list, All(z, alpha,
            Le(delta, Call("apply", qone, v, z))));
        Formula comparison = All(v, list, All(z, alpha,
            Le(Call("apply", qzero, v, z), Seq(c, Sp, Call("apply", qone, v, z)))));
        Formula tailBudget = All(F.Id("k"), Call("Nat"), Imply(
            Lt(n, F.Id("k")), Le(Call("apply", b, F.Id("k")), Pow(a, F.Id("k")))));
        Formula hypotheses = And(Lt(D(0), delta), Le(D(2), Call("card", alpha)),
            Le(delta, Quotient(D(1), Call("card", alpha))), lower,
            Le(D(0), c), comparison, Call("Legal", b, code), Le(D(0), a),
            tailBudget, Lt(rho, D(1)));
        Formula conclusion = Le(Mass(qzero, hzero, code), Seq(
            Pow(c, n), Sp, Mass(qone, hone, code), Sp, Plus, Sp,
            Quotient(Seq(rho, Sp, Pow(Seq(c, Sp, rho), n)), Seq(D(1), Sp, Minus, Sp, rho))));
        Formula body = All(delta, real,
            All(qzero, rows, All(qone, rows,
                All(hzero, Call("NormalizedRows", qzero), All(hone, Call("NormalizedRows", qone),
                    All(c, real, All(b, Seq(Call("Nat"), Sp, To, Sp, Call("Nat")),
                        All(code, Call("Set", list), All(a, real, All(n, Call("Nat"),
                            Imply(hypotheses, conclusion)))))))))));
        return Disp(All(alpha, Call("Type"), Seq(
            OpenBracket, Call("Fintype", alpha), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", alpha), CloseBracket, Sp,
            OpenBracket, Call("MeasurableSpace", alpha), CloseBracket, Sp,
            OpenBracket, Call("MeasurableSingletonClass", alpha), CloseBracket, Sp, body)));
    }

    private static Formula CertificateFormula()
    {
        Formula d = F.Id("d"), delta = DeltaLower, b = F.Id("b"), nu = F.Id("nu");
        Formula nat = Call("Nat"), rat = Call("Rat"), real = Call("Real");
        Formula alpha = Call("Fin", d), list = Call("List", alpha);
        Formula q = F.Id("q"), h = F.Id("h"), code = F.Id("F");
        Formula gamma = GammaLower, v = F.Id("v"), z = F.Id("z"), mode = F.Id("oneWord");
        Formula modulus = All(F.Id("t"), rat, Imply(Lt(D(1), F.Id("t")),
            All(F.Id("n"), nat, Imply(Le(Call("apply", nu, F.Id("t")), F.Id("n")),
                Le(Call("apply", b, F.Id("n")), Pow(F.Id("t"), F.Id("n")))))));
        Formula hypotheses = And(Le(D(2), d), Lt(D(0), delta),
            Le(delta, Quotient(D(1), d)), modulus, Lt(Call("budgetSum", d, b), D(1)),
            Imply(Seq(mode, Sp, Eq, Sp, Call("true")),
                And(Le(D(3), d), All(F.Id("n"), nat,
                    Seq(Call("apply", b, F.Id("n")), Sp, Eq, Sp, D(1))))));
        Formula lower = All(v, list, All(z, alpha, Le(delta, Call("apply", q, v, z))));
        Formula universal = All(q, Seq(list, Sp, To, Sp, alpha, Sp, To, Sp, real),
            All(h, Call("NormalizedRows", q), Imply(lower,
                All(code, Call("Set", list), Imply(Call("Legal", b, code),
                    Le(gamma, Mass(q, h, code)))))));
        Formula conclusion = Let(gamma, Call("value", Call(
            "qFreeHistoricalRationalCertificate", d, delta, b, nu, mode)), And(
                Lt(D(0), gamma), universal, Le(gamma, Call("historicalGap", delta, b)),
                Imply(Seq(mode, Sp, Eq, Sp, Call("true")),
                    All(F.Id("p"), Seq(alpha, Sp, To, Sp, real),
                        Imply(And(All(z, alpha, Lt(delta, Call("apply", F.Id("p"), z))),
                            Seq(Call("coordinateSum", F.Id("p")), Sp, Eq, Sp, D(1))),
                            Lt(gamma, Call("eta", F.Id("p"))))))));
        return Disp(All(d, nat, All(delta, rat,
            All(b, Seq(nat, Sp, To, Sp, nat), All(nu, Seq(rat, Sp, To, Sp, nat),
                All(mode, Call("Bool"), Imply(hypotheses, conclusion)))))));
    }

    private static Formula Mass(Formula q, Formula h, Formula code) =>
        Call("toReal", Call("apply", Call("trajectoryLaw", q, h),
            Call("compl", Call("deletedSet", code))));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, x, Colon, type, Close, Comma, Sp, body);
    private static Formula Imply(Formula p, Formula q) =>
        Seq(Open, p, Close, Sp, Rightarrow, Sp, Open, q, Close);
    private static Formula Lt(Formula x, Formula y) => Seq(x, Sp, F.Lt, Sp, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula Pow(Formula x, Formula y) =>
        Seq(Open, x, Close, Caret, Grp(y));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Underscore, Grp(y));
    private static Formula Quotient(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula And(params Formula[] xs)
    {
        var joined = new List<Formula>();
        for (int i = 0; i < xs.Length; i++)
        {
            if (i > 0) joined.AddRange([Sp, Land, Sp]);
            joined.AddRange([Open, xs[i], Close]);
        }
        return Seq([.. joined]);
    }
    private static Formula Let(Formula x, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, x, Colon, Eq, Sp, value, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Grp(params Formula[] xs) => F.Grp(xs);
    private static Formula D(params byte[] xs) => F.D(xs);
}
