#! /usr/bin/awk -f
BEGIN {
    RS="\n"
    FS=":"
    in_error = 0
}
{
  if (in_error) {
    if ($0 == "") {
      printf("::error file=%s,line=%s,col=%s::%s\n", file, line, col, msg)
      in_error = 0
    } else {
      msg = msg $0 "%0A"
    }
  } else if (NF == 5 && $4 ~ "error|warning") {
    in_error = 1
    msg = ""
    file = $1
    line = $2
    col = $3
  } else {
    print $0
  }
}
END {
  if (in_error) {
    printf("::error file=%s,line=%s,col=%s::%s\n", file, line, col, msg)
  }
}
