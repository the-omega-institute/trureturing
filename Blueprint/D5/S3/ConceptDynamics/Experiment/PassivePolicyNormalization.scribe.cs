using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class PassivePolicyNormalizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization.result";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting constant passive queries preserves terminal candidate fibers and outputs, "
            + "does not increase any actual cost, and gives a minimax recursion by candidate cardinality.",
        H("Passive Policy Normalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("passive-policy-normalization-and-minimax"),
            DeclarationHandle.Create(Declaration),
            H("Normalization and minimax with zero query costs"),
            StatementSource.FromAuthor(StatementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let C be a finite nonempty set of complete sources in an arbitrary carrier W. "
                        + "Each run retains one source, including any shared noise, environment, "
                        + "or device state encoded in it. Let Q be a finite query family, possibly "
                        + "empty, with response type Y(q) depending on q and fixed readout "
                        + "read(q) from W to Y(q). Every query is available at every candidate set. "
                        + "Queries only read the source: they do not change it, unlock actions, "
                        + "or change the terminal contract.")),
                Paragraph(Text(
                    "A history is a finite list of query-response pairs. An arbitrary raw policy "
                        + "selects either a query or a terminal label from each history. Execution "
                        + "follows the response of the same source at every query. Only actual runs "
                        + "from C must terminate; no termination condition is imposed on impossible "
                        + "histories or sources outside C. Write t(x) and l(x) for the unique "
                        + "terminal history and label of an actual run.")),
                Paragraph(Text(
                    "Terminal labels lie in an arbitrary type L and are decoded by out into a "
                        + "metric space Z with finite distances; F maps sources to their target "
                        + "points in Z. Distinct labels may represent different implementations "
                        + "of the same output. Legal(D,l) and the terminal fee tp(D,l) depend on "
                        + "the candidate set D and label l. The query prices c(q) and terminal "
                        + "fees are natural numbers and may be zero. For a history h, C(h) consists "
                        + "of the sources in C matching every recorded response, and K(h,l) is "
                        + "the sum of its query prices plus tp(C(h),l). Feasible means that each "
                        + "actual run terminates with Legal(C(t(x)),l(x)) and K(t(x),l(x)) at most B.")),
                Paragraph(Text(
                    "Assume a legal label of terminal fee zero at C and at every nonempty "
                        + "one-query response fiber C(q,y). These are the hypotheses freeC and "
                        + "freeReply. A contract providing a free legal stop at every reachable "
                        + "history implies both. The latter contract also supplies the same "
                        + "hypotheses when the result is applied recursively to smaller candidate "
                        + "sets. No optimal terminal label is assumed to exist.")),
                Paragraph(Text(
                    "Every feasible raw policy has a dependent PassiveProtocol tree p and a "
                        + "history decoder d. Put tau(x) = runPassiveProtocol(read,p,x). The tree "
                        + "is pruned: each retained query has strictly smaller candidate sets in "
                        + "all response branches. On every actual run, tau(x) is a sublist of t(x), "
                        + "has length at most the cardinality of C minus one, and decodes to "
                        + "exactly l(x). Thus the output out(l(x)) is unchanged. Equality of "
                        + "compressed terminal histories is equivalent to equality of original "
                        + "terminal histories; the candidate fibers C(tau(x)) and C(t(x)) are "
                        + "equal. Terminal legality and the terminal fee are therefore preserved. "
                        + "The total cost on each source is no larger than its original cost and "
                        + "remains at most B.")),
                Paragraph(Text(
                    "The finite candidate set gives a common fuel bound for all terminating "
                        + "actual runs. Induction on this bound removes a query when its response "
                        + "is constant on the current candidates and otherwise joins the smaller "
                        + "response branches. The equality of terminal-history partitions lets "
                        + "the original labels factor through the compressed histories. "
                        + "Nonnegative query prices give the pathwise cost inequality. Each "
                        + "retained query strictly decreases the positive candidate cardinality, "
                        + "which gives the depth bound.")),
                Paragraph(Text(
                    "For any candidate set D, the risk of a feasible policy is the maximum over "
                        + "x in D of dist(out(l(x)),F(x)). Let V(B,D) be its real infimum over "
                        + "all pointwise terminating feasible policies and V(B,H,D) the infimum "
                        + "with at most H actual queries. Let r(B,D) be the real infimum of the "
                        + "same maximum error over legal labels whose terminal fee is at most B. "
                        + "Free stops make these feasible sets nonempty. Normalization gives "
                        + "V(B,C) = V(B,card(C)-1,C).")),
                Paragraph(Text(
                    "Let A(B,C) contain the queries with at least two realized responses and "
                        + "price at most B, and let C(q,y) be the corresponding nonempty response "
                        + "fiber. The continuation value w(q) is the maximum, over realized "
                        + "responses y, of V(B-c(q),C(q,y)), embedded into the extended "
                        + "nonnegative reals by e = ENNReal.ofReal. The minimax value is the "
                        + "minimum of e(r(B,C)) and the infimum of w(q) over A(B,C). "
                        + "An empty eligible query set contributes positive infinity; otherwise "
                        + "a query attains this finite-family infimum. This does not assert that "
                        + "any stopping radius or policy risk infimum is attained.")),
                Paragraph(Text(
                    "The value equality follows by splitting a pruned tree at its first query "
                        + "and joining choices on its finitely many realizable response fibers. "
                        + "Finite supremum-infimum exchange permits arbitrarily close choices "
                        + "without an optimal-center assumption. For every eligible query, "
                        + "each response fiber has smaller cardinality than C. Cardinality "
                        + "therefore makes the recursion well founded even when c(q) is zero. "
                        + "The extended value U(B,C), defined using the loss e(dist(out(l),F(x))), "
                        + "equals e(V(B,C)) and is not infinity. These statements concern fixed "
                        + "passive queries; they provide no complexity bound for finding a "
                        + "policy or a center and do not cover active actions whose availability "
                        + "or effects depend on history."))),
            DescribeRole.Theorem))));

    private static Formula At(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StatementFormula()
    {
        Formula c = F.Id("C");
        Formula b = F.Id("B");
        Formula q = F.Id("q");
        Formula y = F.Id("y");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula policy = F.Pi;
        Formula p = F.Id("p");
        Formula decoder = F.Id("d");
        Formula oldTrace = At(F.Id("t"), x);
        Formula trace = At(F.Tau, x);
        Formula label = At(F.Id("l"), x);
        Formula decoded = At(decoder, trace);
        Formula oldCandidates = At(c, oldTrace);
        Formula newCandidates = At(c, trace);
        Formula oldCost = Call("K", oldTrace, label);
        Formula newCost = Call("K", trace, decoded);
        Formula card = Call("card", c);
        Formula depth = Seq(card, Minus, D(1));
        Formula value = Call("V", b, c);
        Formula radius = Call("r", b, c);
        Formula eligible = Call("A", b, c);
        Formula replies = Call("answers", c, q);
        Formula child = Call("fiber", c, q, y);
        Formula price = Call("c", q);
        Formula eValue = Call("e", value);
        Formula branch = Call("w", q);
        Formula actionInf = Seq(Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(q, InMacro, eligible), Sp, branch);

        return Disp(new Formula.Aligned([
            Seq(Call("Finite", F.Id("Q")), Land, Sp, c, Neq, Emptyset, Land,
                Call("freeC", c), Land, Call("freeReply", c), Implies),
            Seq(Forall, Sp, policy, Comma, Sp, Call("Feasible", policy, c, b), Implies,
                Exists, Sp, p, Comma, decoder, Comma, Sp, Call("Pruned", c, p), Land),
            Seq(Forall, Sp, x, InMacro, Sp, c, Comma, Sp, decoded, Eq, label, Land,
                Call("out", decoded), Eq, Call("out", label), Land,
                Call("Sublist", trace, oldTrace), Land,
                Call("length", trace), Le, depth, Land),
            Seq(newCandidates, Eq, oldCandidates, Land,
                Call("Legal", newCandidates, decoded), Land,
                newCost, Le, oldCost, Le, Sp, b, Comma),
            Seq(Forall, Sp, x, Comma, z, InMacro, Sp, c, Comma, Sp,
                Open, trace, Eq, At(F.Tau, z), Leftrightarrow, Sp,
                oldTrace, Eq, At(F.Id("t"), z), Close, Semi),
            Seq(value, Eq, Call("V", b, depth, c), Comma),
            Seq(eligible, Eq, OpenBrace, q, InMacro, Sp, F.Id("Q"), Mid,
                D(2), Le, Call("card", replies), Land, price, Le, Sp, b, CloseBrace, Comma),
            Seq(branch, Eq, Max, Underscore, Grp(y, InMacro, replies), Sp,
                Call("e", Call("V", Seq(b, Minus, price), child)), Comma),
            Seq(eValue, Eq, Min, OpenBrace, Call("e", radius), Comma,
                actionInf, CloseBrace, Comma),
            Seq(Forall, Sp, q, InMacro, Sp, F.Id("Q"), Comma, Sp,
                D(2), Le, Call("card", replies), Implies,
                Forall, Sp, y, InMacro, replies, Comma, Sp,
                Call("card", child), Lt, card, Comma),
            Seq(eligible, Eq, Emptyset, Implies, actionInf, Eq, Infty, Comma),
            Seq(eligible, Neq, Emptyset, Implies,
                Exists, Sp, q, InMacro, eligible, Comma, Sp, actionInf, Eq, branch, Comma),
            Seq(eValue, Eq, Call("U", b, c), Neq, Infty, Dot),
        ]));
    }
}
