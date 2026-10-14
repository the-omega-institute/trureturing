using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LinearObjectiveDualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/LinearObjectiveDual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational primal and dual witnesses certify finite linear objective bounds and endpoint optimality.",
        H("Exact Rational Linear Objective Certificates"),
        Blocks(
            Paragraph(Text(
                "A feasible point satisfies a finite rational system A x less than or equal to b. A linear query is evaluated by an exact finite rational sum.")),
            Paragraph(Text(
                "An upper certificate is a nonnegative combination of constraint rows that represents the objective coefficients and whose weighted right-hand side is below the proposed upper value. A lower certificate applies the same construction to the negated objective.")),
            Paragraph(Text(
                "Weak duality proves universal validity. A feasible primal point with the same objective value upgrades validity to exact endpoint optimality. External optimization software may propose both witnesses, while Lean checks every coefficient, sign, sum, and equality.")),
            new DocumentBlock.Section(H("Complete first-zero catalogs and one signed budget"), Blocks(
            Paragraph(Text(
                "The application of section 205.1-205.4 uses the finite weighted-sum argument of weighted_constraint_bound and upper_bound_of_certificate. Its arbitrary real scores use the pinned Mathlib ordered-ring and finite-sum suppliers directly; a rational theorem is not silently instantiated at real coefficients. Its finite catalog conclusions do not supply the prime-source transport stated below.")),
            Paragraph(Text(
                "The complete first-zero application uses every Boolean word of length L except the positive word, with three independent nonnegative coefficients A_w, C_w and P_w for each actual first zero n. Their demands are 1-b_n-e, b_n-e and 1-e. The positive word has a separate coefficient T and demand 1-e. Thus all 3(2^L-1)+1 rows remain, including negative singleton demands, zero-score rows and every multiple-zero word. The reward at output label l is A_w 1[l=0]+C_w 1[l=n]+P_w 1[l=0 or l=n].")),
            Paragraph(Text(
                "In the finite correspondence, index i in Fin L denotes original address i+1, castSucc preserves this numerical address, and the last label L denotes output zero. FirstZero fixes the first false bit and every earlier true bit; no later answer is fixed. The complete N catalog contains empty schedules, singletons and all preselected pairs, with arbitrary labels 0 through L in each of the four cells 00,01,10,11. Repeated addresses have singleton information and reversed pairs permute the cells; both actual requests still count. The complete O catalog contains empty schedules, singletons and increasing stopped pairs with arbitrary labels in cells 0,10,11. The first stopped cell is merged before its label is optimized. In particular an unqueried or earlier label remains legal.")),
            Paragraph(Text(
                "The anchor R=(1,2;1,2,0) outputs the actual early first-zero label and otherwise zero. Put alpha=(1,1,0,...,0;0), r=d(alpha), beta_n=sum_{first0(w)=n}(C_w-A_w), K=sum_w(A_w+C_w+P_w)+T and Q(V)=(beta;K). The full row sum minus the anchor is exactly F_{Q(V)}(b)=sum_n beta_n(b_n-alpha_n)-K e. Delta_C(V) is the maximum of reward_V(D)-V dot r over the complete class C catalog. The embedding of every O output rule into its N pair table gives Delta_O(V)<=Delta_N(V); it does not identify their paid request lists.")),
            Paragraph(Text(
                "For m=L-2, H_L retains 1>=b_1>=...>=b_L>=e>=0, b_2=b_3, (m+3)e<=sum_{j>=3}b_j and b_1+sum_{j>=3}b_j-(m+3)e<=1. A quotient residual may have either sign. A unit representative consists of a full nonnegative V and theta in [0,1] with Delta_N(V)<=1-theta and F_{q-Q(V)}(b)<=theta for every b in H_L. The endpoint theta=1 retains all nonzero zero-cost representatives. Nothing divides by 1-theta.")),
            Paragraph(Text(
                "For a source-independent unit-mass mixture of whole O tables, define p_w(l) by summing the weights of tables that output l on the whole word w. Its expected full reward is sum_w[A_w p_w(0)+C_w p_w(n)+P_w(p_w(0)+p_w(n))]+T p_positive(0). The pair event is disjoint addition of labels zero and n, evaluated on this same law. If the base demands hold everywhere, the correct and pair demands hold wherever their coefficients are nonzero, and the positive demand holds, multiplying by these nonnegative coefficients gives V dot d(b) at most the expected reward. Subtracting the unit-mass anchor gives F_{Q(V)}(b)<=Delta_O(V)<=Delta_N(V). A demand at a zero-score row remains an original constraint, although it contributes zero to this scalar calculation."))
            )),
            new DocumentBlock.Section(H("Growing correct-or-pair support"), Blocks(
            Paragraph(Text(
                "Let J_CP(V) consist of late original addresses with positive total correct or pair score. For 1<=d<m and |J_CP(V)|<=d, pad the retained set containing J_CP(V),1,2 to cardinality d+2 in the original address space. No gap is compressed. Set H_d=3(m+1)-2d, a=(d+3)/H_d and e=d/H_d. The constant profile b_n=a belongs to H_L: its two capacity expressions are ma-(m+3)e=3(m-d)/H_d and (m+1)a-(m+3)e=1, and 0<=e<a<=1.")),
            Paragraph(Text(
                "The count-two subset rule selects one whole table before seeing any answer. With mass 1-a it outputs zero immediately. With mass a it selects a uniform three-subset of the retained addresses plus a last star denoting output zero, queries its two smallest labels increasingly, stops at a queried zero and otherwise guesses the third label. The star is never queried. If the actual first zero n is retained, the output is n exactly when n is selected: all earlier selected addresses answer one, including when n is the final unqueried guess. Every later-zero pattern is allowed. The pinned finite-subset suppliers card_filter_powersetCard_subset, card_powersetCard and Nat.add_one_mul_choose_eq give p_w(n)=3a/(d+3)=a-e.")),
            Paragraph(Text(
                "On every word p_w(0)>=1-a, so all base demands 1-a-e hold. The retained independent pair demand follows from p_w(0)+p_w(n)>=1-e. On the positive word p_positive(0)=1-e. These are simultaneous assertions about one whole-table law. Only omitted late correct and pair rows have no guarantee, and their coefficients are zero. Consequently every such full score satisfies F_{Q(V)}(b)<=Delta_O(V)<=Delta_N(V), with unrestricted base rows, early rows and T."))
            )),
            new DocumentBlock.Section(H("Correct-only support and arbitrary pair rows"), Blocks(
            Paragraph(Text(
                "Let J_C(V) consist of late addresses with positive correct score, with |J_C(V)|=k<=h. For m>=3h+2, put D_h=m-2h+1, c=1/D_h, b_n=(h+1)c and e=hc. Use the complete stopped mixture cR+c sum_{j in J_C(V)} Const_j+[1-(k+1)c]Const_0. Its nonnegative weights sum to one. It uses the actual anchor table and whole constant-output tables, with arbitrary legal guessed labels.")),
            Paragraph(Text(
                "For an early first zero, its correct and zero-label probabilities are c and 1-(k+1)c. For a late first zero n they are c 1[n in J_C(V)] and 1-kc. At the positive word the zero-label probability is 1-kc. Thus every base row meets 1-(2h+1)c; every pair row, including one in an omitted late class, meets 1-kc>=1-e; and every retained correct row meets c=b_n-e. Only omitted correct rows lack a guarantee and have zero coefficient. The H_L capacity expressions are (m-3h)c and 1. The same formulas include h=0,m>=2 with J_C(V) empty."))
            )),
            new DocumentBlock.Section(H("One common point, additive cost and closure"), Blocks(
            Paragraph(Text(
                "At either support profile, fix that single b once. For any finite decomposition q=sum_i Q(V_i)+q_res with the indicated component support bound and F_{q_res}(b)<=theta, exact quotient linearity gives F_q(b)<=sum_i Delta_C(V_i)+theta for C=N or O. The full H_L is nonempty and compact: its defining linear equalities and inequalities are closed, and it lies in the finite cube 0<=e<=b_n<=1. The continuous finite-coordinate functional attains its maximum there, so sigma_H is exactly the maximum of F_{q_res} over the full H_L. Its image is bounded above by sum_n |beta_n|+|K|, since 0<=e<=b_n<=1 and 0<=alpha_n<=1. Its bound by theta is equivalent to the bound at every H_L point, and supplies this pointwise residual bound because b belongs to H_L. No hull restriction is imposed on the residual. No residual coordinate has a sign restriction. Different components may use different whole-table mixtures to prove their scalar bounds; they are evaluated at the same b and are not asserted to provide one joint acquisition law.")),
            Paragraph(Text(
                "For a fixed L and fixed support profile b, q maps continuously to F_q(b). Hence every limit in the finite-dimensional quotient space of additive certificates whose total cost is at most B lies in the closed half-space F_q(b)<=B. The profile and B remain fixed in this closure assertion. For an actual complete allocation lambda>=0 with G_N lambda>=h(b) and mass M, the original single-budget argument instead gives F_q(b)<=M Delta_N(V)+theta<=max(1,M). The same lambda supplies every row in that calculation."))
            )),
            new DocumentBlock.Section(H("Dense fair-suffix input and complete catalog excess"), Blocks(
            Paragraph(Text(
                "For m=L-2>=2 and mu>=2, the dense input has C_{1^{j-1}0v}=mu/2^(L-j) at every late class j>=3 and every full suffix v, P_{01v}=P_{10v}=2(mu-1)/2^(L-2), T=mu-1 and A=0. Add arbitrary nonnegative early correct coefficients of total E. These definitions specify actual rows, rather than only first-zero totals or pair marginals. They give W=E+5(mu-1) and K=m mu+W. No common suffix is required for the added early score.")),
            Paragraph(Text(
                "The complete-word reindexing sends a word to its unique actual first zero and its entire suffix; its inverse fixes all preceding bits to one, the first zero to zero, and keeps every suffix bit free. Existence of a first zero is equivalent to the word being different from the positive word. The last first-zero class has one empty suffix. Equiv.ofBijective, Fintype.sum_equiv and Fintype.sum_sigma reindex the actual coefficient sums. The resulting suffix calculation is as follows. For any original i<j and first zero n, average an arbitrary two-bit cell function over every suffix of 1^{n-1}0v. If n<i, all four queried cells have probability 1/4. If n=i, cells 00 and 01 have probability 1/2. If i<n<j, cells 10 and 11 have probability 1/2. If n=j, all mass is in 10. If j<n, all mass is in 11. These are per candidate output label: the full mass of all classes after j is not a single label reward. The empty suffix and arbitrary gaps are included.")),
            Paragraph(Text(
                "For the pair coefficients, the supported actual words are exactly the two prefix families 01v and 10v with every v of length m. The map from a prefix bit and full suffix to these words is a bijection onto the different-first-two-bit words. Finset.sum_subtype and Equiv.sum_comp therefore give sum_w P_w f(w)=2s[average_v f(01v)+average_v f(10v)], and total pair mass 4s. These are identities of the actual coefficient sums. Writing s=mu-1, the zero-label pair-and-positive baseline is (0,2s,2s,s) on (1,2), and (s,s,s,2s) on every other distinct increasing pair. Every legal output label is bounded cellwise by respectively (0,2s,2s,mu) and (s,s,mu,2s). Early labels earn subsets of the pair baseline; late labels use the preceding five-case suffix table. The inequalities mu/2<=s and mu<=2s use the full hypothesis mu>=2. Each candidate correct label earns only its own first-zero class. For an early label its pair reward is a subset of the pair baseline. For a late label its pair reward vanishes, since different first-two-bit words have an early first zero. The zero label receives the complete pair baseline and T at the positive cell. On (1,2), every late first-zero class lies in 11; on any other pair, only the 10 cell can exceed its baseline, by at most one. Thus the cellwise bound totals 5s+1 for every full-label table. A stopped table is embedded by giving 00 and 01 the same label; the embedding respects the merged stopped cell and does not introduce a paid request.")),
            Paragraph(Text(
                "Every complete N constructor has the output rule of a distinct increasing pair table: a constant ignores both answers, a singleton ignores one answer, a repeated pair uses the diagonal, and reversal transposes the two answers. This output comparison bounds rewards while every actual request remains counted by its original schedule. The actual stopped table (1,2;1,2,j), for any late j, obtains all pair mass 4s and the entire correct mass mu of class j; it receives no positive reward. Its total is 4s+mu=5s+1. The anchor receives pair mass 4s and positive reward s, totaling 5s. Hence Delta_N(Y)=Delta_O(Y)=1. For arbitrary early correct rows, write their gain at a table D as sum_{n(w)<=2} C_w 1[D(w)=n(w)]. It lies between zero and E. Both the anchor and the stopped attainer output the correct label on every early-first-zero word and gain exactly E. The same unit excess therefore holds with arbitrary early suffix dependence."))
            )),
            new DocumentBlock.Section(H("Dense-input consequences at the shared profiles"), Blocks(
            Paragraph(Text(
                "At a constant profile b_n=a, the dense quotient evaluation is m mu(a-e)-5(mu-1)e-E(1-a+e). At the correct-or-pair profile it is [3m mu-5d(mu-1)-E(3m-2d)]/[3(m+1)-2d]. Substitution m=2d and mu=4E+3 gives 8d/(4d+3)>1, equal to 8/5 for d=3. Substitution E=0,mu=2,d=m-2 gives (m+10)/(m+7)>1. These actual quotient evaluations and the support inequalities force respectively at least d+1 and m-1 late correct-or-pair labels in every unit representative, and the stated lower additive costs.")),
            Paragraph(Text(
                "For correct-only support, write mu=z+2 with z>=0. The same quotient evaluation is 1+[m-3h-1+z(m-5h)-E(m-2h)]/(m-2h+1). At E=z=0, h=floor((m+1)/3)-1 is admissible and gives a positive numerator, including the h=0 endpoint. Thus a cost-one certificate must have at least floor((L-1)/3) late correct labels in one representative or in one component. For h>=1, m=5h+1 and z=E(3h+1)+1 give excess evaluation (2h+1)/(3h+2) above one. For fixed h,m,E with m>5h and m>=3h+2, its coefficient of z is strictly positive: for every real B there is z>=0 whose full nonnegative dense score still has Delta_N=Delta_O=1 and whose every finite h-correct-support decomposition, with any signed residual of support budget theta, has both N and O additive costs strictly above B. The H_L point depends only on m and h, so remains common as z varies. Rowwise decompositions exist with finite N and O additive costs at each parameter when h>=1: assign one score to each complete event row, so every component has at most one late correct label and their quotient sum is Q(Y).")),
            Paragraph(Text(
                "All dense inputs have the unrestricted candidate (V,theta)=(Y,0) by their unit catalog excess. The obstruction concerns bounded-support additive strategies; it does not exclude E_N or prove a universal N/O separation."))
            )),
            new DocumentBlock.Section(H("Original-source scope"), Blocks(
            Paragraph(Text(
                "The original carrier is the countable prime-labeled source (r,g), with r prime, ceil(F_r/10)<=g<=floor(F_r/5), N(r,g)=1+F_r g, static replies 1[p_i divides N(r,g)] and the original Fibonacci recurrence. Its full tape space is the disjoint union of B_j and P_j blocks, each a copy of (0,1), with measurable marks theta_j=(B_1,1/(j+2)). The consumer and original nonatomic targets retain their original meaning. The separately selected laws are lambda_x^a=(1-a_n(x)) delta_theta_0+a_n(x) delta_theta_n(x), for every positive monotone amplitude sequence bounded by one and tending to zero. There is zero advice, one source-independent common uniform seed, actual sourcewise almost-sure finite handoff and uniform TV over all actual sources and all Borel events.")),
            Paragraph(Text(
                "The original realization interface asks for a fixed interval partition of one U in [0,1), choosing the whole table before replies and then making its class-appropriate requests and emitting an original mark. For two class allocations it permits two partitions of that same U and their common refinement; it does not require equal outputs at each seed. The retained and R-plus-constants mixtures provide only partial-row guarantees and therefore do not alone supply a full acquisition at a target cap. Dual coefficients and fair-suffix score weights are deterministic scores, not a probability law on original sources.")),
            Paragraph(Text(
                "The original finite-to-Borel equivalence additionally requires actual sources for every finite Boolean pattern, contraction of TV under output projection, a common-seed schedule-tail event, finite execution cutoffs and compactness of the full catalog simplex for the closed endpoint. At the closed cap e>0, the active length must be max({n:a_n>e} union {0}), and the transport must prove the actual-tail identity TV=max(1-p_positive(0),a_n), including a_n=e and immediate base output when the active length is zero. Positive-word bookkeeping does not add an infinite all-positive source. These original-source transport obligations are unverified by this finite application. They are needed to infer original acquisition feasibility, but are not premises of the finite dual support obstruction. The unrestricted all-profile comparison remains unresolved. Auxiliary zero-cap H_L points are not asserted to be original positive-tail models."))
            )),
            Describe.Lean(
                DescribeId.Create("upper-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "upper_bound_of_certificate"),
                H("A rational upper dual certificate proves a universal bound"),
                StatementSource.FromAuthor(UpperBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every feasible primal point, the nonnegative weighted constraint sum equals the objective and is bounded by the certificate right-hand side."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "lower_bound_of_certificate"),
                H("A rational lower dual certificate proves a universal bound"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certificate represents the negated objective, so exact weak duality yields the claimed lower bound after reversing the sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-lower-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_lower_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact lower endpoint"),
                StatementSource.FromAuthor(ExactLowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dual witness supplies universal validity and the primal witness supplies attainment at the same exact rational value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-upper-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_upper_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact upper endpoint"),
                StatementSource.FromAuthor(ExactUpperFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem packages the proof obligation required for certified linear-program endpoint sharpness."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula UpperBoundFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula upper = F.Id("u");
        Formula point = F.Id("x");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            upper, Comma, Sp,
            Call("UpperBoundCertificate", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp, Forall, Sp, point, Comma, Sp,
            Call("LinearFeasible", rows, bounds, point), Sp, Rightarrow, Sp,
            Call("linearObjective", objective, point), Sp, Le, Sp, upper, Dot));
    }

    private static Formula LowerBoundFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula lower = F.Id("l");
        Formula point = F.Id("x");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            lower, Comma, Sp,
            Call("LowerBoundCertificate", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp, Forall, Sp, point, Comma, Sp,
            Call("LinearFeasible", rows, bounds, point), Sp, Rightarrow, Sp,
            lower, Sp, Le, Sp, Call("linearObjective", objective, point), Dot));
    }

    private static Formula ExactLowerFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula lower = F.Id("l");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            lower, Comma, Sp,
            Call("LowerBoundCertificate", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp,
            Call("PrimalWitness", rows, bounds, objective, lower), Sp,
            Rightarrow, Sp,
            Call("IsExactLowerBound", rows, bounds, objective, lower), Dot));
    }

    private static Formula ExactUpperFormula()
    {
        Formula rows = F.Id("A");
        Formula bounds = F.Id("b");
        Formula objective = F.Id("c");
        Formula upper = F.Id("u");
        return Disp(Seq(
            Forall, Sp, rows, Comma, Sp, bounds, Comma, Sp, objective, Comma, Sp,
            upper, Comma, Sp,
            Call("UpperBoundCertificate", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp,
            Call("PrimalWitness", rows, bounds, objective, upper), Sp,
            Rightarrow, Sp,
            Call("IsExactUpperBound", rows, bounds, objective, upper), Dot));
    }
}
