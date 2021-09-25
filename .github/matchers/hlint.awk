#! /usr/bin/awk -f
BEGIN {
    RS="\n"
    FS=":"
    in_hint = 0
}
{
  if (in_hint) {
    if ($0 == "") {
      printf("::%s file=%s,line=%s,col=%s::%s\n", sev, file, line, col, msg)
      in_hint = 0
    } else {
      msg = msg $0 "%0A"
    }
  } else {
    in_hint = 1
    file = $1
    if (NF == 4) {
      match($2, "", groups)
      line = groups[1]
      col = groups[2]
      type = $3
      msg = substr($4, 1) "%0A"
    } else if (NF == 5) {
      line = $2
      col = $3
      type = $4
      msg = substr($5, 1) "%0A"
    }
    sev = "error"
    if (type !~ "Error") {
      sev = "warning"
    }
  }
}
END {
  if (in_hint) {
    printf("::%s file=%s,line=%s,col=%s::%s\n", sev, file, line, col, msg)
  }
}
