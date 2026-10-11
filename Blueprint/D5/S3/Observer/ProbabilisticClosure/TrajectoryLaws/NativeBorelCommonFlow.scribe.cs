using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeBorelCommonFlowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.";

    public DocumentDefinition Create()
    {
        Formula flow = F.Id("F"), q = F.Id("Q"), w = F.Id("W");
        Formula pset = F.Id("P"), bset = F.Id("S");
        Formula n = F.Id("n"), i = F.Id("i");
        Formula c = Call("C", flow), l = Call("L", flow), mu = Call("nuP", flow);
        Formula g = F.Id("g"), cb = Fraction(Num(9), Num(25));
        Formula normalized = Call("normalizedIterate", flow, g, Num(3), q);
        Formula defect = Call("threeStepDefect", flow, q);
        Formula f = F.Id("f"), f1 = F.Id("f1"), f2 = F.Id("f2");
        Formula zb = Fraction(Num(6), Num(25));
        Formula iteration = All(Equal(Call("coordinate", n, i, q),
            Call("iterate", l, Call("coordinate", Num(0), i), n, q)),
            ("n", "Nat"), ("i", "Letter"));
        Formula completion = Equal(Call("g", q), Times(
            Seq(Open, Sub(Num(1), Call("u", q)), Close), Call("BIntegral", flow, q,
                Call("oneMinusV"))));
        Formula wordStatement = All(And(Equal(Call("measureComp", c, mu), mu),
            And(Ae(mu, q, iteration), Ae(mu, q, completion))), ("F", "CommonFlow"));
        Formula rows = All(And(Le(Call("smul", Fraction(Num(1), Num(5)),
            Call("row", c, q)), Call("row", l, q)),
            Le(Call("row", l, q), Call("smul", Fraction(Num(4), Num(15)),
                Call("row", c, q)))), ("Q", "PDescriptor"));
        Formula bounded = And(Le(cb, Call("g", q)), And(
            Le(Call("g", q), Fraction(Num(4), Num(9))),
            Le(Call("iterate", l, g, Num(3), q), Times(cb, Pow(zb, Num(3))))));
        Formula normalizedStep = All(Imp(Call("Measurable", f),
            Equal(Call("normalizedIterate", flow, f, Seq(n, Plus, Num(1)), q),
                Call("normalizedAction", flow,
                    Call("normalizedIterate", flow, f, n), q))),
            ("F", "CommonFlow"), ("f", "PDescriptorFunction"), ("n", "Nat"),
            ("Q", "PDescriptor"));
        Formula actionAdd = All(Imp(Call("Measurable", f1),
            Equal(Call("normalizedAction", flow, Seq(f1, Plus, f2), q),
                Seq(Call("normalizedAction", flow, f1, q), Plus,
                    Call("normalizedAction", flow, f2, q)))),
            ("F", "CommonFlow"), ("f1", "PDescriptorFunction"),
            ("f2", "PDescriptorFunction"), ("Q", "PDescriptor"));
        Formula averageAction = All(Equal(Call("normalizedAction", flow,
                Call("threeStepAverage", flow, q), q),
            new Formula.Fraction(Seq(Call("normalizedIterate", flow, g, Num(1), q), Sp, Plus, Sp,
                Call("normalizedIterate", flow, g, Num(2), q), Sp, Plus, Sp,
                Call("normalizedIterate", flow, g, Num(3), q)), Num(3))),
            ("F", "CommonFlow"), ("Q", "PDescriptor"));
        Formula boundsStatement = All(And(rows, Ae(mu, q, bounded)), ("F", "CommonFlow"));
        Formula coreStatement = All(ThereExists(
            And(Call("MeasurableSet", pset), And(Call("MeasurableSet", bset),
            And(Ae(mu, q, Call("Member", q, pset)),
            And(Ae(Call("nuB", flow), w, Call("Member", w, bset)),
            And(All(Imp(Call("Member", q, pset), And(Call("goodP", flow, q),
                Ae(Call("BRow", flow, q), w, Call("Member", w, bset)))),
                ("Q", "PDescriptor")),
                All(Imp(Call("Member", w, bset), And(Call("goodB", flow, w),
                Ae(Call("ARow", flow, w), q, Call("Member", q, pset)))),
                ("W", "BDescriptor"))))))),
            ("P", "PSet"), ("S", "BSet")), ("F", "CommonFlow"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Acquired common flows on full legal-tail probability descriptors.",
            H("Full laws and the acquired return"), Blocks(
                Paragraph(Text("ValidTail(p) consists of every complete word pWord(n,i) and the infinite noncompletion outcome. ValidTail(beta) consists of betaStop, every alpha-prefixed pWord(n,i), and noncompletion. These are the legal full-tail carriers of NativeFullResidual, whose renderer retains original operation blocks and complete-law total variation. The source samples one positive depth in {1,2,3}, with rates 1/3, 2/5 and 3/8, before any paid Read; the analysis below introduces no observer registers.")),
                Paragraph(Text("RegularDescriptor(s) is a probability law on ValidTail(s), with emission in [1/3,2/5] and every source tail inequality at rate 4/15. The suspended tail has the additional factor 2/5. Its measurable structure is inherited from the Giry evaluation structure. Equality of this structure with complete-law-TV Borel is not asserted by the statements here.")),
                Paragraph(Text("CommonFlow contains the original probability measures GammaB and GammaA, their four common unweighted margins nuP and nuB, and the same exhibited Markov disintegrations B and A. Both complete-atom endpoint boxes are included, including noncompletion. The residual contract equates (1-u(Q)) inverse times the prefix-deleted input law to the full B barycenter, and v(W) inverse times the prefix-deleted input law to the full A barycenter. The legal-word partitions then reconstruct the input measure: law(Q)=u(Q) delta_alpha+(1-u(Q)) map(prependB,barycenter(B(Q))); law(W)=(1-v(W)) delta_beta+v(W) map(prependA,barycenter(A(W))). Barycenters are full opposite laws, without opposite regularity requirements. prependB and prependA restore the deleted original letter and preserve noncompletion.")),
                Paragraph(Text("C is A composed after B. L weights the A row by v(W) and the resulting B composition by 1-u(Q). Thus its action is (Lf)(Q)=(1-u(Q)) integral v(W) integral f(Qprime) A(W,dQprime) B(Q,dW). iterate(L,f,0)=f and iterate(L,f,n+1) is integration of iterate(L,f,n) against the L row. coordinate(n,i,Q) is Q{pWord(n,i)} and g(Q)=coordinate(0,1,Q). AE(mu,Q,P) denotes P for mu-almost every Q; BIntegral(F,Q,oneMinusV) denotes the integral of 1-v under the original B row. measureComp, row and smul denote measure composition, kernel evaluation and nonnegative measure scaling.")),
                Node("common-flow-word-iteration", "common_flow_word_iteration",
                    "Both entire word families", wordStatement,
                    "The disintegrations and common margins make nuP stationary for C. Evaluating the two full residual identities at each complete word gives the one-return recurrence. L is dominated by C, so stationarity transports the null exceptions through every iterate. Countable conjunction yields one full-measure set for every index and bit. At the first marker-one word, reconstruction gives the completion integral."),
                Node("common-flow-operator-bounds", "common_flow_operator_bounds",
                    "Uniform row bounds and the upper three-return box", boundsStatement,
                    "Emission bounds place 1-u in [3/5,2/3] and v in [1/3,2/5]. Positivity of the acquired integrals gives the two measure inequalities and completion bounds. The original endpoint word masses from FourthSegmentStoppedLaw give c_a z_a^3 below c_b z_b^3, with c_b=9/25 and z_b=6/25. The full p box therefore bounds the third L iterate of g. These are conditional integrals; no assertion bounds individual sampled path products."),
                Node("common-flow-conull-core", "common_flow_conull_core",
                    "A closed conull realization", coreStatement,
                    "PSet is Set(PDescriptor) and BSet is Set(BDescriptor); Member is set membership, and BRow and ARow are the original acquired kernel rows. The predicate goodP(F,Q) conjoins the full normalized B residual equality, the full p endpoint box, both entire coordinate iteration formulas, the completion integral, 9/25 <= g <= 4/9, and iterate(L,g,3,Q) <= (9/25)(6/25)^3. The predicate goodB(F,W) conjoins the full normalized A residual equality and the full suspended endpoint box. The measurable sets P and S have full nuP and nuB measure and satisfy these predicates pointwise. Every Q in P has B(Q)-almost every successor in S, and every W in S has A(W)-almost every successor in P. Starting from measurable hulls of the null exceptions, successive sets exclude positive-probability predecessors. The two unweighted margin identities keep every exclusion null. Their countable intersections are closed under both original kernels; no transition-closure hypothesis is imposed."),
                Node("common-flow-normalized-third-step", "common_flow_normalized_third_step",
                    "Normalized third return bound", All(Ae(mu, q, Le(normalized, cb)), ("F", "CommonFlow")),
                    "normalizedIterate(F,f,n,Q) is endpointRate⁻¹ raised to n times iterate(L,f,n,Q). The theorem transports the full p endpoint-box inequality at depth three through the exact scalar normalization endpointRate=6/25; it retains the original arbitrary Borel descriptor and acquired L operator."),
                Node("common-flow-three-step-defect-nonneg", "common_flow_three_step_defect_nonneg",
                    "Three-step defect is nonnegative", All(Ae(mu, q, Le(Num(0), defect)), ("F", "CommonFlow")),
                    "threeStepDefect is the truncated ENNReal difference (g−normalizedIterate(L,g,3))/3. Its nonnegativity is recorded on the same full-measure endpoint-box core; it is the finite-block input for the later Jensen/localization construction. No harmonicity, survivor event, or limit is asserted here."),
                Node("common-flow-normalized-iterate-succ", "normalizedIterate_succ",
                    "Normalized action advances one return", normalizedStep,
                    "The scalar endpoint normalization commutes with one L integration. The measurable iterate witness is discharged from the same Borel kernel, and no new state or transition is introduced."),
                Node("common-flow-normalized-action-add", "normalizedAction_add",
                    "Normalized action preserves nonnegative addition", actionAdd,
                    "Kernel integration and endpoint scaling preserve addition for the measurable first summand. This is the linearity input needed when the finite-block average is expanded; it does not assert a Jensen or localization conclusion."),
                Node("common-flow-normalized-action-average", "normalizedAction_threeStepAverage",
                    "Normalized action of the finite-block average", averageAction,
                    "The acquired normalized action sends the three-step average to the corresponding three successive normalized iterates. This is an exact finite algebraic bridge for the later localization argument; no fixed point, killing, or limit is claimed."))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Times(Formula a, Formula b) => Multiply(a, b);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Ae(Formula mu, Formula x, Formula body) => Call("AE", mu, x, body);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula ThereExists(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Exists, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, Sp, F.Id(xs[i].Type), Comma, Sp, body);
        return body;
    }
}
