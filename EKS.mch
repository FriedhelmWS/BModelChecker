MACHINE           EKS
/* This B Machine models a simplified electronic key system.
*/
SETS              BOOK; USER; STATUS = {locked, unlocked}; AUTHOR; YEAR

VARIABLES         books, users, users_has_login, users_member, access, author, publish_in, borrowed, has_borrowed, reserved

PROPERTIES		  card(BOOK) = 5

INVARIANT         books : POW(BOOK) & 
                  users : POW(USER) & 
		  users_has_login : POW(USER) & 
		  users_member : POW(USER) & 
                  access : BOOK <-> USER & 
		  author: BOOK <-> AUTHOR &
		  publish_in: BOOK <-> YEAR &
                  dom(access) <: books &
                  ran(access) <: users &
       		  borrowed : POW(BOOK) &
     		  has_borrowed: USER <-> POW(BOOK) &
		  reserved: BOOK +-> USER

INITIALISATION    books := {};
                  users := {};
		  users_has_login := {};
		  users_member := {};
                  access := {};
		  author := BOOK * {};
		  publish_in := BOOK * {};
		  borrowed :={};
		  reserved := {};
   		  has_borrowed:= {}

OPERATIONS
  addbook(kk, aa, yy) = PRE kk:BOOK & kk /: books & aa : AUTHOR & yy:YEAR THEN books := books \/ {kk}; author := author \/ {kk |-> aa}; publish_in := publish_in \/ {kk |-> yy} END;

  deletebook(kk) = PRE kk : books& kk/: borrowed & {kk} <| access = {} THEN books := books - {kk}; author := {kk} <<| author; publish_in := {kk} <<| publish_in ; borrowed := borrowed-{kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END  END;

  adduser(rr) = PRE rr:USER & rr /: users THEN users := users \/ {rr} END;

  deleteuser(rr) = PRE rr : users & access |> {rr} = {} & (has_borrowed={}or has_borrowed(rr)={}) THEN users := users - {rr}; has_borrowed:={rr} <<| has_borrowed  END;

  userlogin (uu) = PRE uu : users & uu/: users_has_login THEN users_has_login := users_has_login \/ {uu}; IF uu : dom(has_borrowed) THEN has_borrowed := has_borrowed ELSE has_borrowed := has_borrowed \/ {uu |-> {}} END END;

  buymember (uu) = PRE uu : users & uu: users_has_login & uu: users_has_login & uu/: users_member THEN users_member := users_member \/ {uu} END;

  userlogout (uu) = PRE uu : users & uu: users_has_login THEN users_has_login := users_has_login - {uu} END;

  borrowbook(kk,uu) = PRE kk:BOOK & kk:books & kk/: borrowed & uu:users & uu:users_has_login & ( kk/: dom(reserved) or (kk: dom(reserved) & reserved(kk)=uu)) THEN borrowed := borrowed \/ {kk}; has_borrowed(uu) := has_borrowed(uu)\/{kk}; IF kk: dom(reserved) THEN reserved:= {kk} <<| reserved END END;

  returnbook(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk:has_borrowed(uu) & uu:users & uu:users_has_login THEN borrowed := borrowed - {kk}; has_borrowed(uu) := has_borrowed(uu)-{kk} END;

  reservebook(kk,uu) = PRE kk:BOOK & kk:books & kk: borrowed & kk /: has_borrowed(uu) & uu:users & uu:users_has_login & kk/: dom(reserved)THEN reserved := reserved \/ {kk |-> uu}END;

  output <-- Search_author(aa) = PRE books /= {}& aa:AUTHOR THEN output:=author |> {aa} END;

  output <-- Search_year(yy) = PRE books /= {}& yy:YEAR THEN output:=publish_in |> {yy} END


END
