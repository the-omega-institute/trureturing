using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstZeroRecursionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact first-zero necessity and bounded constructive sufficiency on actual prefix cells.",
        H("FirstZeroRecursion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kbonacci-first-zero-necessity"),
                DeclarationHandle.Create(Owner + "first_zero_necessity"),
                H("Every successful prefix subtree satisfies the first-zero recursion"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("Y"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("f"), Colon, Sp, Seq(Call("Option", Call("LiveRecord",
                    F.Id("k"))), Sp, To, Sp, F.Id("Y")), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("h"),
                    Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("t"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    Sp, F.Id("u"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("S"), Colon, Sp, Call("Set", Call("ZMod", Seq(F.Id("k"),
                    Plus, D(1)))), Comma, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp,
                    Leq, Sp, F.Id("m")), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(F.Id("h"), Plus, Seq(F.Id("t"), Sp, Cdot, Sp,
                    F.Id("m"))), Sp, Eq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(0), Sp, Lt, Sp, F.Id("h")), Close),
                    Sp, Land, Sp, Seq(Open, Call("Nonempty", F.Id("S")), Close)), Close), Sp, Land, Sp, Seq(Open, Call("BoundedReachStrategy",
                    Call("acquisitionSystem", F.Id("k"), F.Id("m"), F.Id("ell"), Call("Option", Call("LiveRecord", F.Id("k")))),
                    Call("targetGoal", F.Id("f")), F.Id("n"), Call("prefixCell", F.Id("k"), F.Id("m"), F.Id("t"), F.Id("h"), F.Id("v"),
                    F.Id("u"), F.Id("S"))), Close)), Close), Sp, Implies, Sp, Seq(Open, Call("FirstZeroCriterion", F.Id("k"),
                    F.Id("m"), F.Id("f"), F.Id("v"), F.Id("t"), F.Id("h"), F.Id("S")), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k>=2, m>=1, either alphabet, arbitrary label type Y "
                        + "and target on optional LiveRecord, initial value v, positive "
                        + "h and natural t with h+tm=k, arbitrary common current value u, "
                        + "nonempty ambient phase set S and finite horizon n, a native "
                        + "successful strategy at prefixCell(k,m,t,h,v,u,S) implies "
                        + "FirstZeroCriterion(k,m,f,v,t,h,S). The cell contains exactly "
                        + "the initial (v,phi,s) and current (u,phi+tm,s+tm) pairs "
                        + "with phi in S and s<h. ClearingCondition requires one common "
                        + "ORIGINAL label on all phases and tails in h-a<=s<h, and "
                        + "a separate common label on each phase's s<h-a fiber. "
                        + "The criterion is true for empty S. Otherwise it selects "
                        + "a<m and a<h satisfying ClearingCondition, or, only when "
                        + "h>m, requires rejection constancy and the criterion at "
                        + "every nonempty incrementChild. The induction covers stopping, "
                        + "all-one blocks, every locally legal first-zero block and "
                        + "internally illegal blocks. Each recursive child is proved "
                        + "equal to its actual endpoint reply fiber in both directions. "
                        + "This theorem is necessity; recursive sufficiency and the "
                        + "whole source theorem's uniform cost are separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-safe-phase-protocol"),
                DeclarationHandle.Create(Owner + "safe_phase_protocol"),
                H("Literal fixed archives decode endpoint subgroup phase"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp,
                    Leq, Sp, F.Id("m")), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Exists, Sp, F.Id("actions"), Colon, Sp,
                    Call("List", Call("AllowedBlock", F.Id("k"), F.Id("m"), F.Id("ell"))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Call("length", F.Id("actions")), Sp, Eq, Sp, Call("phaseCost", F.Id("k"), F.Id("m"))), Close), Sp, Land,
                    Sp, Seq(Open, Seq(Forall, Sp, F.Id("v1"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("v2"), Colon, Sp,
                    Call("ZMod", D(2)), Comma, Sp, F.Id("phi1"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp,
                    F.Id("phi2"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s1"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("s2"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Seq(Open, Seq(F.Id("s1"), Sp, Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s2"), Sp,
                    Lt, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Call("divides", Call("gcd", F.Id("m"), Seq(F.Id("k"),
                    Plus, D(1))), Call("val", F.Id("phi1"))), Close), Sp, Land, Sp, Seq(Open, Call("divides", Call("gcd", F.Id("m"),
                    Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi2"))), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("v1"), Sp,
                    Eq, Sp, F.Id("v2")), Close), Sp, Land, Sp, Seq(Open, Seq(Call("fixedBlockArchive", F.Id("actions"), Call("some",
                    F.Id("v1"), F.Id("phi1"), F.Id("s1"))), Sp, Eq, Sp, Call("fixedBlockArchive", F.Id("actions"), Call("some",
                    F.Id("v2"), F.Id("phi2"), F.Id("s2")))), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(F.Id("phi1"), Sp,
                    Eq, Sp, F.Id("phi2")), Close)), Close)), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k>=2, m>=1 and either alphabet there exists a fixed list of "
                        + "allowed complete blocks of length phaseCost(k,m). For any two "
                        + "live records with tails below k, phases in P, and equal scalar "
                        + "values, equality of the two actual fixedBlockArchive lists "
                        + "implies equal phases. phaseCost is zero for p=1, p-1 for "
                        + "m>=2 and p>1, 2T for m=1 with odd T, and 2T+1 for m=1 "
                        + "with even T. The lists are respectively empty, repeated "
                        + "isolatedProbe(m,j), the single-bit pairs (01)^T, and "
                        + "(01)^(T/2) 0 (01)^(T/2). Initial scalar equality is the "
                        + "free endpoint baseline. Prefix execution connects each "
                        + "sample in the list to the literal phase recovery supplier. "
                        + "The exported conclusion is exact length and phase separation at equal "
                        + "visible baselines; it does not add a separate universal survival "
                        + "conjunct or a total decoder. No clock reading is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-first-zero-sufficiency"),
                DeclarationHandle.Create(Owner + "first_zero_sufficiency"),
                H("First-zero recursion constructs an actual bounded strategy"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("Y"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("f"), Colon, Sp, Seq(Call("Option", Call("LiveRecord",
                    F.Id("k"))), Sp, To, Sp, F.Id("Y")), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("h"),
                    Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("t"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    Sp, F.Id("u"), Colon, Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("S"), Colon, Sp, Call("Set", Call("ZMod", Seq(F.Id("k"),
                    Plus, D(1)))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")),
                    Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp, Leq, Sp, F.Id("m")), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(F.Id("h"),
                    Plus, Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m"))), Sp, Eq, Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(D(0),
                    Sp, Lt, Sp, F.Id("h")), Close), Sp, Land, Sp, Seq(Open, Call("Nonempty", F.Id("S")), Close)), Close), Sp,
                    Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("phi"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma,
                    Sp, Seq(Open, Seq(Seq(Open, Seq(F.Id("phi"), Sp, InMacro, Sp, F.Id("S")), Close), Sp, Implies, Sp, Seq(Open,
                    Call("divides", Call("gcd", F.Id("m"), Seq(F.Id("k"), Plus, D(1))), Call("val", F.Id("phi"))), Close)), Close)),
                    Close), Sp, Land, Sp, Seq(Open, Call("FirstZeroCriterion", F.Id("k"), F.Id("m"), F.Id("f"), F.Id("v"), F.Id("t"),
                    F.Id("h"), F.Id("S")), Close)), Close), Sp, Implies, Sp, Seq(Open, Call("BoundedReachStrategy", Call("acquisitionSystem",
                    F.Id("k"), F.Id("m"), F.Id("ell"), Call("Option", Call("LiveRecord", F.Id("k")))), Call("targetGoal", F.Id("f")),
                    Call("prefixBudget", F.Id("k"), F.Id("m"), F.Id("h")), Call("prefixCell", F.Id("k"), F.Id("m"), F.Id("t"),
                    F.Id("h"), F.Id("v"), F.Id("u"), F.Id("S"))), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary Y and f on Option LiveRecord, k>=2, m>=1, "
                        + "either alphabet, h>0, h+t*m=k, nonempty S contained in P, "
                        + "and any common current value u, FirstZeroCriterion implies "
                        + "a native bounded strategy on prefixCell(k,m,t,h,v,u,S). "
                        + "Its horizon is floor((h-1)/m)+1+phaseCost(k,m). A clearing "
                        + "witness a issues exactly 1^a 0^(m-a). Rejection cells stop "
                        + "with their common ORIGINAL target. Surviving cells decode "
                        + "the actual protocol-start phase and cancel the known "
                        + "(t+1)*m shift before applying each initial-phase label "
                        + "constancy condition. Empty R_0 supplies no label witness. "
                        + "A recursive witness issues U and constructs a continuation "
                        + "on each attained reply cell, proving its exact equality "
                        + "with the smaller prefixCell. The recursion decreases h "
                        + "by m and its child horizon plus one equals the parent "
                        + "horizon. The goal retains initial sources through every "
                        + "transition; there is no decidable equality premise on Y."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
