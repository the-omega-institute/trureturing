using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FixedPositivePartitionSseDistanceDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(variables[i].Name.Value), Colon, Sp,
                variables[i].Domain, Comma, Sp, body);
        return body;
    }
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        for (var i = types.Length - 1; i >= 0; i--)
            body = Seq(OpenBracket, types[i], CloseBracket, Comma, Sp, body);
        return body;
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Endpoint(Formula h, Formula p) => Call("partitionMatrix", h, p);
    private static Formula Chain(Formula h, Formula p, Formula r, Formula l) =>
        Call("ExchangeChain", Call("MonoidAlgebra", F.Id("Nat"), h), Endpoint(h, p), Endpoint(h, r), l);
    private static Formula GroupFamily(Formula body, bool nontrivial = false)
    {
        Formula h = F.Id("H");
        Formula[] instances = nontrivial
            ? [Call("Group", h), Call("Fintype", h), Call("Nontrivial", h)]
            : [Call("Group", h), Call("Fintype", h)];
        return All(Instances(body, instances), B("H", F.Id("Type")));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed positive group-ring partition family has exact maximum-coordinate exchange distance.",
        H("Fixed positive partition exchange distance"), Blocks(
            Describe.Lean(DescribeId.Create("fixed-positive-partition-exact-distance"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2"),
                H("The entire fixed partition family"),
                StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let H be a finite nontrivial group, q its order, u the sum of its group elements, and write z(H)=q1-u in the integer group ring. Here smul denotes natural-number scalar multiplication, and toNat converts each integer coefficient to a natural number. A partition p of n is padded to n decreasing coordinates. Its nilpotent shift is the direct sum of the upper Jordan shifts of these lengths, flattened by prefix sums. Thus the coordinates and endpoint depend only on p.")),
                    Paragraph(Math(Disp(CenteredUniform()))),
                    Paragraph(Math(Disp(EndpointEntries()))),
                    Paragraph(Text("The displayed integer group-ring entries are strictly positive and hence determine natural group-ring entries. The baseline q cubed times n is fixed throughout the family.")),
                    Paragraph(Text("For neighboring partitions, rectangular zero-one block factors P and Q multiply to their respective shifts. Empty blocks are allowed. Flattening uses the two independent prefix-sum coordinates. The group-ring factors U=qJu+Pz and V=qJu+Qz have strictly positive natural coefficients and their actual products are the two endpoints. The fixed-mass partition geodesic therefore gives a chain of the exact displayed length, including length zero.")),
                    Paragraph(Text("For the lower bound, RectangularNilpotenceBarrier.exchange_chain_lag supplies the shared cumulative intertwining maps R and S for every competing rectangular chain; their two products are the endpoint powers of its length L. This reuses the original cumulative proof from theorem32_2, with no separate new-content credit. Intermediate dimensions may change and may be zero. Act on the kernel of rational augmentation, whose rational dimension is q-1. The uniform element annihilates this ideal, and the endpoint acts as q squared times its partition shift on each ideal coordinate.")),
                    Paragraph(Text("For the endpoint operators T and Q, set I=im(T to the j), M=S(I), and N=im(T to the j+L). The map R from M onto N intertwines the restrictions. It induces an actual surjection from M/QM onto N/TN. Rank-nullity and the embedding of the kernel on M into the kernel on im(Q to the j) compare the endpoint layer dimensions.")),
                    Paragraph(Math(Disp(LayerBound()))),
                    Paragraph(Text("Explicit endpoint shift coordinates evaluate each layer as q-1 times the number of partition parts exceeding its threshold. Cancel q-1, which is positive. Taking j equal to each part of the opposite partition proves the coordinate bound in both directions. Their maximum gives the lower bound on every chain length. No classification or partition assumption is imposed on the intermediate matrices.")),
                    Paragraph(Text("The prescribed single-chain subfamily.")),
                    Paragraph(Text("Fix n at least two. For each t from one to n, take the actual padded partition p_t=(t,1,...,1,0,...,0), with n-t ones and t-1 zeros. Its length and total mass are both n. Use the existing prefix-sum block coordinates, without changing the endpoint numbering. In these coordinates its partition shift is literally T_t: the only nonzero entries are (a,a+1) for one-based indices 1<=a<t. Let D_t have ones in its first t-1 diagonal positions and zeros elsewhere, and let J be the n by n all-one matrix.")),
                    Paragraph(Math(Disp(SingleChainMatrices()))),
                    Paragraph(Text("Here every displayed integer group-ring matrix is interpreted coefficientwise in the natural group ring after positivity is proved. An activated entry of either factor has coefficient 2q-1 at the identity and q-1 elsewhere; every inactive entry has coefficient q. Each coefficient of A_t is at least q cubed times n minus q, which is positive. The identities u squared=qu, uz=zu=0 and z squared=qz, together with D_t T_t=T_t and T_t D_t=T_(t-1), give the actual products U_t V_t=A_t and V_t U_t=A_(t-1). The fixed partition endpoint is therefore this literal A_t.")),
                    Paragraph(Math(Disp(SingleChainPowers()))),
                    Paragraph(Text("The power formula holds for every positive j. The entry of T_t to the j at (a,b) is one exactly when b=a+j and b<=t, and is zero otherwise. Thus T_t to the t is zero, while every positive power below t has its (1,1+j) entry equal to one. Augmentation kills z, so the actual augmentation matrix is q to the fourth times n times J. The uniformity threshold is exactly t. In particular the action of H on the actual stationary dimension group of A_t is the identity: advancing a representative by t stages multiplies it by a uniform matrix, which makes each group translate equal in the direct limit. This supplies inertness of the constructed matrix rather than assuming it.")),
                    Paragraph(Text("Rectangular competitors and the same four maps.")),
                    Paragraph(Text("For the general depth bound, put e=u/q in the rational group ring. It is central and idempotent, and the map x to (1-e)x equals x-e times its augmentation. This map preserves addition, zero and multiplication, including rectangular matrix products. Applying it to an arbitrary natural group-ring SSE chain gives a chain between the actual augmentation-zero endpoint matrices. The rectangular nilpotence barrier gives a<=b+L and b<=a+L for their exact positive depths a,b. Intermediate dimensions may vary and may be zero; no essentiality or intermediate inertness is needed.")),
                    Paragraph(Text("Starting at A_t, use the displayed factors successively in decreasing t, and interchange them for the increasing direction. This prescribes a Type-valued chain of length D=|t-r| with its actual cumulative matrices R,S. The padded-partition distance is D. The partition lower bound applies to every competing rectangular chain and to arbitrary R,S satisfying all four SE equations, so D is the minimum SSE length, and for unequal endpoints it is the minimum positive SE lag. At t=r the prescribed chain transports to the nil chain and its history map is the identity.")),
                    Paragraph(Text("Choose a numbering of the finite group once. Use its induced order and the same whole-fibre rank at every occurrence of R and S in matrixPhiR, matrixPhiS, matrixPsi0 and matrixPsiL. Conjugating the original recursive sweeps by these ranks cancels the adjacent inverse rank maps at every step. Hence these literal sweeps satisfy both long equations, both positive-lag alignment equations and both balance equations. FixedCutCoherence.full_overlap and full_inverse_coherence then give both complete overlap and inverse laws at every extra length on these same maps. An arbitrary complete compatible, aligned or balanced certificate gives its own four SE equations by counting each total-label fibre; its positive lag is consequently at least D.")),
                    Paragraph(Text("Actual histories and every positive period.")),
                    Paragraph(Text("Apply OrderedGroupChainHistories to that prescribed chain. Its actual expanded bilateral histories are related by the constructed history homeomorphism f, with continuous inverse, shift equivariance and H equivariance. In anchored coordinates it is (x,h) to (F(x),h gamma(x)), where gamma is the ordered product of the transfers along this same chain; the inverse uses gamma(F inverse(y)) inverse. For every signed time i, the forward value at i depends only on input times from i to i+D, and the inverse value only on times from i-D to i. Consequently, for every natural N both centered observations q_N after these maps factor through q_(N+D). The sharper forward window is [-N,N+D] and the sharper inverse window is [-N-D,N]. These statements include D=0 and make no claim that the displayed windows are minimal among all conjugacies.")),
                    Paragraph(Text("For every h in H and every positive j, twistedPeriod_card counts the actual h-twisted histories by the corresponding diagonal group coefficients of A_t to the j. Every positive power of T_t has zero diagonal, including when j<t. The nonuniform term in the displayed power formula therefore contributes zero to this count at every positive j, not only after uniformization.")),
                    Paragraph(Math(Disp(SingleChainPeriods()))),
                    Paragraph(Text("The right-hand side is independent of t. For each d from zero to n-1, the two members t=1 and r=d+1 lie in this same full observation fibre and have prescribed-presentation distance d. Numbering and the discrete topology are constructed choices for a finite group, not extra order or topological-group hypotheses; the chosen numbering is used throughout the four maps and history formulas."))),
                DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("rational-shift-equivalence-bound"),
                    DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.rational_shift_equivalence_bound"),
                    H("Arbitrary shift equivalences bound the partition distance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Let H be finite and nontrivial, n be positive, and p,r be any padded partitions of n. Let X,Y be arbitrary rational group-ring n by n matrices and let L be any natural number. Assume only the four shift-equivalence equations: A(p)X=XA(r), A(r)Y=YA(p), XY=A(p)^L and YX=A(r)^L. Then dInf(p,r)<=L. In particular, no competing exchange chain is an input, and natural positive SE data are covered by their rational coefficient cast.")), Paragraph(Text("The original quotient-layer proof is used twice, once in each direction. The original endpoint action evaluates the two image-rank filtrations, and the original coordinate-bound argument gives the maximum-coordinate bound. The existing theorem32_2 now consumes this chain-free result after extracting its cumulative factors. This theorem does not identify the prescribed single-chain matrices or construct aligned certificates."))),
                    DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula h = F.Id("H"), n = F.Id("n"), p = F.Id("p"), r = F.Id("r"), l = F.Id("L");
        Formula distance = Call("dInf", p, r);
        return GroupFamily(All(Imp(Le(D(1), n),
                And(Call("Nonempty", Chain(h, p, r, distance)),
                    Par(All(Imp(Chain(h, p, r, l), Le(distance, l)), B("L", F.Id("Nat")))))),
            B("n", F.Id("Nat")), B("p", Call("Partition", n)),
            B("r", Call("Partition", n))), nontrivial: true);
    }

    private static Formula CenteredUniform()
    {
        Formula h = F.Id("H");
        return GroupFamily(Equal(Call("z", h),
            Sub(Call("smul", Call("card", h), D(1)), Call("uniform", h))));
    }

    private static Formula EndpointEntries()
    {
        Formula h = F.Id("H"), n = F.Id("n"), p = F.Id("p");
        Formula i = F.Id("i"), j = F.Id("j"), q = Call("card", h);
        return GroupFamily(All(Equal(Call("partitionMatrix", h, p, i, j),
                Call("toNat", Add(
                    Call("smul", Mul(Call("power", q, D(3)), n), Call("uniform", h)),
                    Call("smul", Mul(q, Call("partitionShift", p, i, j)), Call("z", h))))),
            B("n", F.Id("Nat")), B("p", Call("Partition", n)),
            B("i", Call("Fin", n)), B("j", Call("Fin", n))));
    }

    private static Formula SingleChainMatrices()
    {
        Formula q = F.Id("q"), n = F.Id("n"), u = F.Id("u"), z = F.Id("z");
        Formula j = F.Id("J"), t = F.Id("t"), shift = Call("T", t);
        return And(Equal(Call("A", t), Add(Mul(Mul(Mul(Call("power", q, D(3)), n), j), u),
                Mul(Mul(q, z), shift))),
            And(Equal(Call("U", t), Add(Mul(Mul(q, j), u), Mul(z, Call("D", t)))),
                Equal(Call("V", t), Add(Mul(Mul(q, j), u), Mul(z, shift)))));
    }

    private static Formula SingleChainPowers()
    {
        Formula q = F.Id("q"), n = F.Id("n"), j = F.Id("j"), t = F.Id("t");
        Formula uniformPart = Mul(Mul(Mul(Call("power", q, D(3)), n), F.Id("J")), F.Id("u"));
        return Equal(Call("power", Call("A", t), j),
            Add(Call("power", uniformPart, j),
                Mul(Mul(Call("power", q, Sub(Mul(D(2), j), D(1))), F.Id("z")),
                    Call("power", Call("T", t), j))));
    }

    private static Formula SingleChainPeriods()
    {
        Formula q = F.Id("q"), n = F.Id("n"), j = F.Id("j"), t = F.Id("t");
        return Equal(Call("F", F.Id("h"), j, Call("A", t)),
            Call("trace", Call("power", Mul(Mul(Call("power", q, D(4)), n), F.Id("J")), j)));
    }

    private static Formula LayerBound()
    {
        Formula v = F.Id("V"), w = F.Id("W"), t = F.Id("T"), q = F.Id("Q");
        Formula r = F.Id("R"), s = F.Id("S"), l = F.Id("L"), j = F.Id("j");
        Formula rational = F.Id("Rational");
        Formula Rank(Formula f, Formula k) =>
            Call("finrank", rational, Call("range", Call("power", f, k)));
        Formula premises = And(Equal(Call("comp", t, r), Call("comp", r, q)),
            And(Equal(Call("comp", q, s), Call("comp", s, t)),
                Equal(Call("comp", r, s), Call("power", t, l))));
        Formula bound = Le(Sub(Rank(t, Add(j, l)), Rank(t, Add(Add(j, l), D(1)))),
            Sub(Rank(q, j), Rank(q, Add(j, D(1)))));
        return All(Instances(All(Imp(premises, Par(All(bound, B("j", F.Id("Nat"))))),
                B("T", Call("End", rational, v)), B("Q", Call("End", rational, w)),
                B("R", Call("LinearMap", rational, w, v)),
                B("S", Call("LinearMap", rational, v, w)), B("L", F.Id("Nat"))),
            Call("AddCommGroup", v), Call("Module", rational, v), Call("FiniteDimensional", rational, v),
            Call("AddCommGroup", w), Call("Module", rational, w), Call("FiniteDimensional", rational, w)),
            B("V", F.Id("Type")), B("W", F.Id("Type")));
    }
}
