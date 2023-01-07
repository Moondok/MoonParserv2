#ifndef UTIL_H
#define UTIL_H
const unsigned int WIDTH=1200;
const unsigned int HEIGHT=900;

#include<iostream>
/*********************判断是否为字母********************/
bool isLetter(char letter);

/*****************判断是否为数字************************/
bool isDigit(char digit);
bool isOct(char digit);
bool isHex(char digit);
bool isDelimiter(char ch);
bool isOperator(char ch);


#endif // UTIL_H
